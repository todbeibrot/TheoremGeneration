import warnings
from ray.util.annotations import RayDeprecationWarning
import os
from gymnasium import Env
from utils.voc import Vocabulary, merge_worker_vocabularies
from utils.storage import version_name, latest_version, latest_version_path, next_version, next_version_path
from env import TheoremGenerationEnv
import ray
from ray import tune
from ray.rllib.algorithms.ppo import PPOConfig
from ray.tune.registry import register_env
import pathlib
from pprint import pprint
from ray.air.integrations.wandb import WandbLoggerCallback
from ray.rllib.algorithms.callbacks import DefaultCallbacks
import wandb
from ray.tune.schedulers import PopulationBasedTraining
import random
from functools import partial
from ray.rllib.examples.rl_modules.classes.action_masking_rlm import ActionMaskingTorchRLModule
from ray.rllib.core.rl_module.rl_module import RLModuleSpec
from model import SmallAttentionModule
from action_mask import ActionMaskingSmallAttentionModule

# -------------------------------------------------
# Run configuration
# -------------------------------------------------
iterations = 20
vocabulary_update_interval = 2
checkpoint_interval = 100
tuning_samples = 1
continue_run = False
hyperparameter_tuning = False
hyperparameter_tuning = hyperparameter_tuning and not continue_run and tuning_samples > 0
use_wandb = True
use_wandb_tune = False
debug_env = False

# Paths
file_path = pathlib.Path(__file__)
root = file_path.parent.resolve()
run_version = next_version("run", "runs")
run_directory = next_version_path("run", "runs").resolve()
last_run_directory = latest_version_path("run", "runs")
models_path = run_directory / "models"
log_path = run_directory / "logs"
tune_path = run_directory / "tune"
vocabulary_path = run_directory / "vocabulary"
project = "theorem_generation"
tune_project = "theorem_generation_tune"
run_name = f"run_{run_version}"


# -------------------------------------------------
# Env
# -------------------------------------------------
register_env("theorem_generation_env", lambda env_config: TheoremGenerationEnv(**env_config))

if continue_run:
    vocabulary_load_path = vocabulary_path
else:
    vocabulary_load_path = root / "data" / "vocabularys"

vocabulary = Vocabulary(save_path=vocabulary_path, load_path=vocabulary_load_path)
vocabulary_copy = vocabulary.get_mapping()

if debug_env:
    env = TheoremGenerationEnv(vocabulary=vocabulary_copy)
    print("debugging env build")

env_config = {
    "vocabulary": vocabulary_copy
}


# -------------------------------------------------
# Callbacks
# -------------------------------------------------

tune_callbacks = []
callbacks = []

if use_wandb_tune:
    tune_callbacks.append(WandbLoggerCallback(
        project=tune_project,
        excludes=[
            "config",
            "hist_stats",
            "sampler_results",
            "info",
        ],
        **({"name": run_name, "reinit": "finish_previous"})
    ))


if use_wandb:
    class WandbCallback(DefaultCallbacks):

        def __init__(self):
            super().__init__()
            self.custom_metrics = ["truncated"]


        def on_train_result(self, *, algorithm, result, **kwargs):
            try:
                learner = result["learners"]["default_policy"]
                learner_all = result["learners"]["__all_modules__"]
                env_runner = result["env_runners"]

                log = {
                    "reward/mean": env_runner["episode_return_mean"],
                    "reward/max": env_runner["episode_return_max"],
                    "reward/min": env_runner["episode_return_min"],

                    "episode/length": env_runner["episode_len_mean"],
                    "episode/duration_sec": env_runner["episode_duration_sec_mean"],

                    "steps": env_runner["num_episodes"] * env_runner["episode_len_mean"],
                    "episodes": env_runner["num_episodes"],
                }
                log.update({
                    "ppo/policy_loss": learner.get("policy_loss"),
                    "ppo/value_loss": learner.get("vf_loss"),
                    "ppo/kl_loss": learner.get("mean_kl_loss"),
                    "ppo/value_loss_unclipped": learner.get("vf_loss_unclipped"),
                    "ppo/total_loss": learner.get("total_loss"),
                    "ppo/entropy": learner.get("entropy"),
                    "ppo/value_explained_var": learner.get("vf_explained_var"),
                    "ppo/training_steps": learner_all.get("num_env_steps_trained"),
                })

                for metric in self.custom_metrics:
                    log[f"env/{metric}"] = env_runner.get(metric)

                # Filter None
                log = {k: v for k, v in log.items() if v is not None}
    
                wandb.log(log)
     
            except Exception as e:
                print("WandB logging failed:", e)

        # Custom infos
        def on_episode_end(self, *, episode, metrics_logger, **kwargs):
            last_info = episode.get_infos()[-1]
            for metric, value in last_info.items():
                if metric in self.custom_metrics:
                    metrics_logger.log_value(metric, value, reduce="mean", window=50)


class VocabCallback(DefaultCallbacks):

    def __init__(self, update_interval, save_path, load_path):
        super().__init__()
        self.vocabulary = Vocabulary(save_path, load_path)
        self.vocabulary_id = 0
        self.vocabulary_copy = self.vocabulary.get_mapping()
        self.update_interval = update_interval
        self.new_tokens = set()

    def on_train_result(self, *, algorithm, **kwargs):
        if algorithm.training_iteration % self.update_interval == 0:
            self.update_vocabularys()

    def on_episode_created(self, *, env, env_index, **kwargs):
        e = env.envs[env_index].unwrapped
        self.collect_tokens(e)
        self.update_env_vocabulary(e)

    def collect_tokens(self, env):
        # Collect tokens
        new_tokens = env.consume_new_tokens()
        self.new_tokens.update(new_tokens)

    def update_vocabularys(self):
        if self.new_tokens:
            # Update central vocabulary
            self.vocabulary.merge_tokens(self.new_tokens)
        self.new_tokens = set()
        self.vocabulary_copy = self.vocabulary.get_mapping()
        self.vocabulary_id += 1

    def update_env_vocabulary(self, env):
        new_vocabulary = self.vocabulary.get_mapping()
        env.update_vocabulary(new_vocabulary, self.vocabulary_id)


callbacks.append(WandbCallback)
callbacks.append(partial(VocabCallback, vocabulary_update_interval, vocabulary_path, vocabulary_load_path))


# -------------------------------------------------
# Algorithm
# -------------------------------------------------

config = (
    PPOConfig()
    .environment(
        env="theorem_generation_env",
        env_config=env_config
    )
    # .environment("Humanoid-v5")
    .framework("torch")
    .env_runners(
        num_env_runners=1,
        num_envs_per_env_runner=1,
        #remote_worker_envs=None,
        #rollout_fragment_length=2**9,
        #sample_timeout_s=300,
        add_default_connectors_to_env_to_module_pipeline=True,
        add_default_connectors_to_module_to_env_pipeline=True
    )
    .reporting(
        # min_time_s_per_iteration=2,
        # min_sample_timesteps_per_iteration=10000
    )
    .rl_module(
        rl_module_spec=RLModuleSpec(
            module_class=SmallAttentionModule,
            model_config = {
                "vocab_size": 200,
                "embed_dim": 64,
                "num_heads": 2,
                "num_layers": 1
            }
        )
    )
)

if hyperparameter_tuning:
    config = config.training(
        use_gae=True, 
        use_critic = True,
        gamma=tune.uniform(0.95, 0.999),
        entropy_coeff=tune.loguniform(1e-4, 1e-2)
    )
else:
    config = config.training(
        use_gae=True, 
        use_critic = True,
        gamma=0.995,
        lr=0.0001,
        clip_param=0.2,
        train_batch_size_per_learner=256,
        minibatch_size=128,
        num_epochs=10
    )

# -------------------------------------------------
# Start ray and WandB
# -------------------------------------------------

print("init ray")
ray.init()

# -------------------------------------------------
# Tuning
# -------------------------------------------------
if hyperparameter_tuning:
    def explore(config):
        # ensure we collect enough timesteps to do sgd
        if config["train_batch_size"] < config["sgd_minibatch_size"] * 2:
            config["train_batch_size"] = config["sgd_minibatch_size"] * 2
        # ensure we run at least one sgd iter
        if config["num_sgd_iter"] < 1:
            config["num_sgd_iter"] = 1
        return config

    hyperparam_mutations = {
        "clip_param": lambda: random.uniform(0.01, 0.5),
        "lr": [1e-3, 5e-4, 1e-4, 5e-5, 1e-5],
        "num_epochs": lambda: random.randint(1, 30),
        "minibatch_size": lambda: random.randint(2**7, 2**13),
        "train_batch_size_per_learner": lambda: random.randint(2**11, 2**17),
    }

    print("hyperparameter tuning")
    tuner = tune.Tuner(
        "PPO",
        param_space=config,
        run_config=tune.RunConfig(
            storage_path=tune_path,
            stop={"training_iteration": 30},
            callbacks=tune_callbacks,
            verbose=0
        ),
        tune_config=tune.TuneConfig(
            num_samples=tuning_samples,
            trial_dirname_creator=lambda trial: f"trial_{trial.trial_id}",
            # reuse_actors=True,
            metric="env_runners/episode_return_mean",
            mode="max",
            scheduler=PopulationBasedTraining(
                time_attr="time_total_s",
                perturbation_interval=120,
                resample_probability=0.25,
                # Specifies the mutations of these hyperparams
                hyperparam_mutations=hyperparam_mutations,
                custom_explore_fn=explore,
            ),
            # time_budget_s= 1 * 60
        ),
    )

    results = tuner.fit()
    best_result = results.get_best_result()


config = config.callbacks(
    callbacks
)

# -------------------------------------------------
# Training loop
# -------------------------------------------------

print("build algo")
algo = config.build_algo()
if continue_run:
    model_path = latest_version_path("checkpoint", last_run_directory / "checkpoints").resolve()
    algo.restore_from_path(model_path)
elif hyperparameter_tuning:
    algo.from_checkpoint(best_result.checkpoint)

wandb.init(
    project=project,
    name=run_name,
    dir=log_path
)

print("-" * 40)
print("-" * 40)
print("-" * 40)
print("training start")
for i in range(iterations):
    result = algo.train()

    # pprint(result)

    if i % checkpoint_interval == 0:
        checkpoint_path = next_version_path("checkpoint", run_directory / "checkpoints").resolve()
        checkpoint = algo.save_to_path(checkpoint_path)
        print("Checkpoint saved at", checkpoint)

algo.stop()