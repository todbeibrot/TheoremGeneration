import REPL.Main

open Lean

-- comes with set debugging input
/-- Main executable function, run as `lake exe repl_test`. -/
unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  repl_test
