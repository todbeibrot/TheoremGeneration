import Lean
import REPL.TheoremM.Apply

/- This file is only for debugging. Simple API with examples serving as input (commands and tactics) for the repl.
Can be used via "lake exe repl_test".  -/

def start : String := "{\"path\": \"REPL/TheoremM/TheoremGeneration.lean\"}"
def tac (s : String) (proofState : Nat) : String := s!"\{\"proofState\": {proofState}, \"tactic\": \"{s}\"}"
def intro                     := tac "intro"
def intros                    := tac "intros"
def apply        (s : String) := tac s!"apply  {s}"
def apply'       (s : String) := tac s!"apply' {s}"
def close_goal                := tac "close_goal"
def add_variable              := tac "add_variable"
def add_function              := tac "add_function"
def add_prop                  := tac "add_prop"
def add_type     (n : Nat)    := tac s!"add_type {n}"
def rotate_right              := tac "rotate_right"
def rotate_left               := tac "rotate_left"
def infer_instance            := tac "infer_instance"
def assumption                := tac "assumption"
-- TODO: check automatic infer_instance

def tactics1 : List (Nat → String) :=
  [add_type 2, apply' "Eq", rotate_right, apply' "x98", apply' "Add.add", close_goal, apply' "Add.add", assumption,
   apply' "x98", apply' "x98", apply' "x98", apply' "Type", apply' "Add.add"]

def tactics2 : List (Nat → String) :=
  [add_type 2, apply' "Eq", rotate_right, apply' "x98", intro, add_variable, apply' "Add",
   add_prop, apply' "Eq", apply' "x99", apply' "x98", apply' "x97",
   apply' "x99", assumption, apply' "x98", apply' "x98"]

def tactics3 : List (Nat → String) :=
  [add_function, apply' "True", apply' "False", close_goal]

def tactics_trivial : List (Nat → String) :=
  [rotate_left, apply' "True"]

def tactics_aux (tactic_list : List (Nat → String)) : List String := start :: (tactic_list.zip [0 : tactic_list.length].toList).map (fun (x, n) => x n)
def tactics : List String := tactics_aux tactics3
