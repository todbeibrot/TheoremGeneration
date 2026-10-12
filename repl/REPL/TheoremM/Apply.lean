import Lean

open Lean Meta Elab Tactic Term

namespace Mathlib.Tactic

-- TODO: this is in mathlib.
-- this can be deleted and be replaced with the mathlib version as soon as we integrate mathlib to this project

/--
`apply (config := cfg) e` is like `apply e` but allows you to provide a configuration
`cfg : ApplyConfig` to pass to the underlying `apply` operation.
-/
elab (name := applyWith) "apply" " (" &"config" " := " cfg:term ") " e:term : tactic => do
  let cfg ← unsafe evalTerm ApplyConfig (mkConst ``ApplyConfig) cfg
  evalApplyLikeTactic (·.apply · cfg) e

macro (name := applyWith') "apply' " e:term : tactic =>
  `(tactic|
    apply (config := { allowSynthFailures := true, newGoals := ApplyNewGoals.all }) $e
  )

end Mathlib.Tactic
