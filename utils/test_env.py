from gymnasium import Env
from utils.voc import Vocabulary, merge_worker_vocabularies
from env import TheoremGenerationEnv

def test_env(env: TheoremGenerationEnv, vocab: Vocabulary, steps=1000, merge_interval=100):

    """
    env   : environment instance
    vocab : central Vocabulary
    """
    step_by_step = False
    print_step = 50

    obs, info = env.reset()
    reset = 0

    for step in range(steps):
        if step % print_step == 0:
            print("-" * 20)
            print(f"step {step}")
        if step_by_step:
            user_input = input(f"step {step}")

        # sample random action
        action = env.action_space.sample()

        try:
            obs, reward, terminated, truncated, info = env.step(action)
        except Exception:
            env.render()
            print(f"last reset: {reset}")
            raise

        # reset episode if needed
        if terminated or truncated:
            print("_" * 20)
            print("reset")
            obs, info = env.reset()
            reset = step

        # periodically merge vocabulary
        if step % merge_interval == 0:
            new_tokens = env.consume_new_tokens()
            vocab.merge_tokens(new_tokens)
            vocab.save()
            env.update_vocabulary(vocab.get_mapping())

    env.close()


if __name__ == "__main__":
    vocab = Vocabulary()
    env = TheoremGenerationEnv(vocabulary=vocab.get_mapping())

    test_env(env, vocab, steps=10000, merge_interval=100)