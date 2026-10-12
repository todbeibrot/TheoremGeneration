from lean_interact import LeanREPLConfig, LeanServer, Command, ProofStep, FileCommand
from lean_interact.server import LeanError
import gymnasium as gym
from gymnasium import spaces
import numpy as np
import sys
from pathlib import Path



class TheoremGenerationEnv(gym.Env):
    

    def __init__(self, vocabulary):
        super().__init__()

        # Debugging
        self.print_tokens = False
        self.print_tactic = False
        self.print_state  = False

        # Parameters
        self.max_input_length = 200
        self.max_tokens = 200
        self.max_variables = 20
        self.max_steps = 10
        self.verbose = 0
        # time in seconds until we abort a lean command
        self.timeout = 5

        # Create a configuration for the Lean REPL
        root = Path(__file__).resolve().parents[0]
        repl_path = root / "repl"
        lean_config = LeanREPLConfig(local_repl_path=repl_path)
        nat_lean_config = LeanREPLConfig()
        # Start the Lean servers
        # The first server will be used for the interaction with the environment. It uses custom observations for reinforcement learning.
        self.lean_server = LeanServer(lean_config)
        # The second server will be used by the LLMs. It is a classical Lean instance without any changes. 
        self.nat_lean_server = LeanServer(nat_lean_config)

        # Vocabulary
        self.vocabulary = vocabulary
        self.vocabulary_id = 0
        self.new_tokens = set()

        # Actions
        self.defs = ["And", "Or", "False", "True", "Not", "Id"]
        # Free variables in Lean. Some will be reused if we run out of variable names.
        self.variables = [f"x{var}" for var in range(self.max_variables)]
        tactics = [
            "add_variable",
            "add_function",
            "add_prop",
            "close_goal",
            "rotate_left",
            "rotate_right",
            "intro",
            "constructor",
            "assumption"
        ]
        tactics_add_type = ["add_type <number>"]
        tactics_with_number = ["apply' <number>"]
        tactics_with_def = ["apply' <def>"]
        tactics_with_variable = ["apply' <var>"]

        self.actions = tuple(
            tactics
            + [t.replace("<number>", str(n)) for t in tactics_with_number   for n in range(10)]
            + [t.replace("<number>", str(n)) for t in tactics_add_type      for n in range( 3)]
            + [t.replace("<def>",    d)      for t in tactics_with_def      for d in self.defs]
            + [t.replace("<var>",    v)      for t in tactics_with_variable for v in self.variables]
        )
        self.n_actions = len(self.actions)

        # Define action and observation spaces
        self.action_space = spaces.Discrete(self.n_actions)
        self.observation_space = spaces.Dict({
            "tokens": spaces.MultiDiscrete([self.max_tokens] * self.max_input_length),
            "depths": spaces.Box(
                low=0.0,
                high=1.0,
                shape=(self.max_input_length,),
                dtype=np.float32,
            )
        })
        # self.observation_space = spaces.Box(
        #     low=-1.,
        #     high=1.,
        #     shape=(2 * self.max_input_length,),
        #     dtype=np.float32
        # )
        # self.observation_space = spaces.Discrete(3)

        # Action Masking
        # We don't want to repeat failed actions or use actions requiring undefined lean variables.
        self.observation_space = spaces.Dict({
            "action_mask": spaces.Box(0.0, 1.0, shape=(self.n_actions,)),
            "observations": self.observation_space 
        })

        # Variables used in the tactic space. actions depending on nonexisting variables will be masked.
        self.used_variables = set()
        self.update_masked_actions()

        # Starts the theorem generation via a file in lean.
        response = self.lean_server.run(FileCommand(path="REPL/TheoremM/TheoremGeneration.lean"))
        sorry = response.sorries[0]
        # The goal is 'Prop'
        self.initial_goals = sorry.goal
        self.initial_proofstep_id = sorry.proof_state
        self.initial_obs = self.obs(self.initial_goals)
        self.metrics = {}



    def reset(self, seed=None, options=None):
        super().reset(seed=seed)
        self.step_count = 0

        # Reset the proof state
        self.proof_state_id = self.initial_proofstep_id
        self.goals = self.initial_goals
        self.proof_status = "Incomplete"

        info = {"truncated": 0}
        self.state = self.initial_obs

        # Variables used in the tactic space. actions depending on nonexisting variables will be masked.
        self.used_variables = set()
        self.update_masked_actions()
        # Actions which have been used on the current tactic state and failed. 
        # We will mask those actions.
        self.failed_actions = set()

        self.metrics = info
        return self.state, info

    def step(self, action):
        # Validate action if needed
        assert self.action_space.contains(action), f"Invalid action: {action}"
        if action in self.masked_actions:
            print("masked action used")

        self.step_count += 1
        truncated = self.step_count >= self.max_steps

        info = {"truncated": int(truncated)}

        # Proof step
        self.tactic = self.actions[action]
        if self.print_tactic:
            print(self.tactic)
        if self.tactic in self.masked_actions:
            if self.print_state:
                print("masked action")
            return self.state, 0., False, truncated, info
        proof_step = ProofStep(tactic=self.tactic, proof_state=self.proof_state_id)
        proofstep_response = self.lean_server.run(proof_step, timeout=self.timeout)

        if isinstance(proofstep_response, LeanError):
            # This is an unexected error inside Lean. 
            # Stop this episode with 0. reward to prevent this in the future.
            if self.print_state:
                print("Lean Error")
            return self.state, 0., True, truncated, info
        proof_status = proofstep_response.proof_status

        if proof_status.__contains__("contains sorry"):
            if self.print_state:
                print("contains sorry")
            self.add_failed_action(action)
            return self.state, 0., False, truncated, info    
        elif proof_status.__contains__("Error"):
            if self.print_state:
                print("error")
            self.add_failed_action(action)
            return self.state, 0., False, truncated, info    

        self.empty_failed_actions()
        self.proof_status = proofstep_response.proof_status
        self.proof_state_id = proofstep_response.proof_state
        self.goals = proofstep_response.goals[0]
        self.messages = proofstep_response.messages
        if self.print_state:
            print(self.goals)
        self.state = self.obs(self.goals)

        # Example reward
        reward = 1.

        # Termination conditions
        terminated = self.proof_status.__contains__("Complete")

        if self.verbose > 0:
            if terminated:
                print(self.proof_status)
            elif truncated:
                print("max steps reached")

        if terminated:
            # Extract the new theorem as a Lean expression
            self.new_theorem_expression = self.messages[0].data

        self.metrics = info
        return self.state, reward, terminated, truncated, info

    def render(self):
        if self.verbose > 0:
            print("render")
            print("-" * 30)
            print(self.tactic)
            print("." * 30)
            print(self.goals)
            print("-" * 30)
        pass

    def close(self):
        pass

    def update_used_variables(self, token_obs):
        self.used_variables = set()
        for variable in self.variables:
            if self.get_id(variable) in token_obs:
                self.used_variables.add(variable)

    def update_masked_actions(self):
        self.masked_actions = set()
        # Mask all action which depend on unused variables.
        # Example: "apply' x15" is only valid if x15 is already defined.
        # If a tactic requires a name for a new variable, we will let the system set it.
        # Afterwards, it will be automatically renamed to "x..." inside Lean.
        for variable in self.variables:
            if variable not in self.used_variables:
                for action in self.actions:
                    if variable in action:
                        self.masked_actions.add(action)
        self.valid_actions = np.ones((self.n_actions))
        for action in self.masked_actions:
            self.valid_actions[self.actions.index(action)] = 0.


    def obs(self, goals: str):
        token_obs = np.zeros(self.max_input_length, dtype=np.int32)
        depth_obs = np.zeros(self.max_input_length, dtype=np.float32)

        i = 0
        for token_with_depth in goals.split("\t"):
            if i >= self.max_input_length:
                break
            token_with_depth = token_with_depth.strip()
            if not token_with_depth:
                continue
            token, depth = token_with_depth.split("\x1E", 1)

            token_obs[i] = self.get_id(token.strip())
            depth_obs[i] = int(depth)

            i += 1
        
        self.update_used_variables(token_obs)

        # maps depth to the interval (0,1)
        mask = depth_obs > 0
        depth_obs[mask] = 1.0 / np.log(depth_obs[mask] + np.e + 1e-8)

        obs = {
            "tokens": token_obs,
            "depths": depth_obs,
        }
        obs = self.obs_add_masked_actions(obs)
        return obs
    
    def obs_add_masked_actions(self, obs):
        return {
            "observations": obs,
            "action_mask": self.valid_actions
        }


    def get_id(self, token):
        if token in self.vocabulary:
            return self.vocabulary[token]

        self.new_tokens.add(token)
        return self.vocabulary["<UNKNOWN>"]
    
    def update_vocabulary(self, new_vocabulary, vocabulary_id):
        if self.vocabulary_id != vocabulary_id:
            self.vocabulary.update(new_vocabulary)
            self.vocabulary_id = vocabulary_id
    
    def consume_new_tokens(self):
        tokens = self.new_tokens
        self.new_tokens = set()
        return tokens
    
    def add_failed_action(self, action):
        self.failed_actions.add(action)
        self.mask(action)

    def mask(self, action):
        self.masked_actions.add(action)
        self.valid_actions[self.actions.index(action)] = 0.

    def empty_failed_actions(self):
        self.failed_actions = set()