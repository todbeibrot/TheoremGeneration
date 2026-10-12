# TheoremGeneration

Work in progress: a Lean 4 reimplementation of [lemma-set](https://github.com/todbeibrot/lemma-set), using reinforcement learning to generate theorems for training a prover.

The central idea is **using tactics to construct theorems**. Lean's tactic monad provides tools for constructing terms interactively. Normally, these tools construct a proof term for a given theorem statement. But a theorem statement is itself a term of type `Prop`: this project uses the same machinery, with some extensions, to construct that statement interactively.

**[`TheoremM`](repl/REPL/TheoremM/TheoremM.lean)** implements these extensions. It maintains the emerging theorem and a shared context across goals, carries this state through tactic steps, and abstracts introduced variables and hypotheses into the final statement.

The agent starts with a goal of type `Prop`. Its central action is **`apply' <definition>`**. Additional custom tactics introduce variables, propositions, types, and functions, or close a goal by introducing a hypothesis. Together, these operations are intended to support constructing a diverse set of theorems from a given set of definitions.

A modified Lean REPL exposes this construction process through a **custom observation of Lean output**, using custom delaborations to output syntax directly and skip the usual conversion into a human-readable string. Because the model is trained from scratch, its input need not follow conventions designed for human readers. The aim is to avoid pretty-printing transformations that add no information, preserve the original information as faithfully as possible, and standardize its representation. The Python side connects this environment to an attention-based policy trained with PPO.

The next step is to integrate a prover and use its estimate of theorem difficulty (value function) to guide generation toward challenging theorems that provide useful training material.
