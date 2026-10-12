import Lean
import REPL.PP.PrettyPrinter
import REPL.PP.Delab

open Lean Meta Elab Term Tactic

namespace TheoremM

structure Context where
  maxVariables := 20
  maxMVarIds   := 99
  maxLVarIds   := 99

/-- Adds global context to the Tactic monad.
    Every meta variable should have access to the context. -/
structure State where
  -- gctx is now the local context of Context.thm
  -- gctx  : LocalContext := {}
  thm : MVarId
  -- standartized names for the level meta variables meant for printing.
  lUserNames : PersistentHashMap LMVarId Name := {}
  /-- Counter for naming hypotheses of thm -/
  hypCounter : Nat := 0
  /-- List of all the tactics which have been tried and failed in the current tactic state.
  They should be empty after a successfull tactic.
  We keep track of the tactics to avoid repeating them. -/
  failedTactics : List (TSyntax `tactic) := []
deriving Inhabited

/-- Our custom tactic monad: `TacticM` + mutable `M.State`. -/
abbrev _root_.TheoremM := ReaderT Context $ StateRefT TheoremM.State TacticM

/- deprecated! use `newHypName` -/
def increaseHypCounter : TheoremM Unit := do
  let s ← get
  set {s with hypCounter := s.hypCounter + 1}

def newHypName : TheoremM Name := do
  let ctx ← read
  let s ← get
  let userName : Name := Name.str Name.anonymous s!"x{ctx.maxVariables - s.hypCounter}"
  set {s with hypCounter := s.hypCounter + 1}
  return userName

def getTheorem : TheoremM MVarId :=
  return (← get).thm

def setTheorem (thm : MVarId) : TheoremM Unit := do
  set {← get with thm := thm}

def setLUserNames (lUserNames : PersistentHashMap LMVarId Name) : TheoremM Unit := do
  let s ← getThe TheoremM.State
  set {s with lUserNames := lUserNames}

def addFailedTactic (stx : Syntax) : TheoremM Unit := do
  let s ← get
  -- TODO double check that it is a tactic
  let typed_stx : TSyntax `tactic := ⟨stx⟩
  set {s with failedTactics := typed_stx :: s.failedTactics}

def deleteFailedTactics : TheoremM Unit := do
  let s ← get
  unless s.failedTactics.isEmpty do
    set {s with failedTactics := []}

/--
Merge `extra` into `base` by re-inserting the `LocalDecl`s.

Notes:
- `LocalContext` is an *ordered set* of `LocalDecl`s, not a list.
- We conservatively skip decls whose `fvarId` already exists in `base`.
- This assumes `extra` is “compatible” (i.e. any dependencies are already in `base`).
- If you later want stronger guarantees, you’ll need a more careful dependency/order policy.
-/
private def mergeLocalContext (base extra : LocalContext) : LocalContext :=
  Id.run do
    let mut acc := base
    for d in extra do
      if acc.find? d.fvarId |>.isSome then
        continue
      else
        acc := acc.addDecl d
    return acc

/--
Make `goal` use the local context and local instances stored in our state.

Implementation:
- read our `M.State`
- mutate the metavariable declaration of `goal` by merging:
  * `lctx := goal.lctx` extended with `state.lctx`
  * `localInstances := goal.localInstances` extended with `state.linst`
- return the same `goal` (the ID doesn’t change; its declaration does)
-/
def liftGoal (goal : MVarId) : TheoremM Unit := do
  let gctx := (← (← get).thm.getDecl).lctx
  goal.modifyDecl fun decl =>
    { decl with lctx := mergeLocalContext decl.lctx gctx }
  return

def liftGoals : TheoremM Unit := do
  let goals ← getGoals
  goals.forM liftGoal

/- prefix followed by one number -/
def checkName (name namePrefix : Name) : Bool :=
  match name with
    | Name.num namePrefix' _ => namePrefix == namePrefix'
    | _ => false

/- match names of the form x0, x42, x666, ... -/
def checkName'' (name namePrefix : Name) : Bool :=
  match (name, namePrefix) with
  | (.str .anonymous s, .str .anonymous pfx) =>
      if s.startsWith pfx then
        let rest := s.drop pfx.length
        !rest.isEmpty && rest.toString.toList.all Char.isDigit
      else
        false
  | _ => false

/- prefix followed by numbers -/
def checkName' (name namePrefix : Name) : Bool :=
  match name with
    | Name.num namePrefix' _ => checkName' namePrefix' namePrefix
    | namePrefix' => namePrefix == namePrefix'

/- expects prefix followed by numbers. replaces this prefix. -/
def changePreFix (name newPrefix : Name) : Name :=
  match name with
    | Name.num namePrefix' n => Name.num (changePreFix namePrefix' newPrefix) n
    | _ => newPrefix

/- Build a map which is used to name all unassigned LMVarIds -/
def setLevelNames : TheoremM Unit := do
  let ctx ← read
  let mctx ← getMCtx
  let mut lUserNames : PersistentHashMap LMVarId Name := {}
  let mut counter := 0

  for (lMVarId, _) in mctx.lDepth do
    if not (← isLevelMVarAssigned lMVarId) then
      lUserNames := lUserNames.insert lMVarId (Name.num `l counter)
      counter := (counter + 1) % ctx.maxLVarIds
  setLUserNames lUserNames

def ppLUserName (lMVarId : LMVarId) : Name :=
  let name := lMVarId.name
  if checkName' name `_uniq then
    changePreFix name `u
  else name

def ppLUserNames : TheoremM Format := do
  let s ← getThe TheoremM.State
  let lUserNames := s.lUserNames
  let ppLUserNames := lUserNames.toList.map
    (fun (lMVarId, lUserName) => (ppLUserName lMVarId, lUserName))
  return format ppLUserNames

/--
Replaces all LMvarIds with their respective username.
-/
def replaceLUserNames (s : String) : TheoremM String := do
  let lUserNames := (← get).lUserNames
  return lUserNames.foldl (init := s) fun str lMvarId name =>
    str.replace (toString lMvarId.name) (toString name)

def setMVarsUserNames : TheoremM Unit := do
  let mctx ← getMCtx
  let ctx ← read
  let mut decls := mctx.decls
  let mut userNames : PersistentHashMap Name MVarId := {}
  let mut userNameId := 0
  for (mVarId, decl) in mctx.decls do
    if ← mVarId.isAssigned then
      continue
    let userName := Name.num `m userNameId
    userNames := userNames.insert userName mVarId
    userNameId := (userNameId + 1) % ctx.maxMVarIds
    decls := decls.insert mVarId {decl with userName := userName}
  setMCtx {mctx with userNames := userNames, decls := decls}

-- checks if all variables in the local context of `mvar` follow our variable naming schema
def correctLocalVarNames (mvarId : MVarId) : TheoremM Bool := mvarId.withContext do
  let lctx ← getLCtx
  for localDecl in lctx do
    if localDecl.isImplementationDetail then
      continue
    let userName := localDecl.userName
    if !checkName'' userName `x then
      return false
  return true

-- renames all variables in the local context of `mvar` to follow our variable naming schema
-- returns the new variable
-- TODO take the variable counter modulo a max value
def renameLocalVarNames (mvarId : MVarId) : TheoremM MVarId := do
  let lctx ← mvarId.withContext do
    -- mvarId.checkNotAssigned `renameLctx
    let mut lctx ← getLCtx
    let mut localDeclId := 0
    for localDecl in lctx do
      if localDecl.isImplementationDetail then
        continue
      lctx := lctx.modifyLocalDecl localDecl.fvarId (·.setUserName (Name.str Name.anonymous s!"x{localDeclId}"))
      localDeclId := localDeclId + 1
    return lctx
  --let mut tag ← mvarId.getTag
  --let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances) (← mvarId.getType) .syntheticOpaque tag
  let MCtx ← getMCtx
  let decl := MCtx.getDecl mvarId
  let new_decl := {decl with lctx := lctx}
  let new_decls := MCtx.decls.insert mvarId new_decl
  let new_MCtx := {MCtx with decls := new_decls}
  --mvarId.assign mvarNew
  --return mvarNew.mvarId!
  setMCtx new_MCtx
  return mvarId

def renameMVars : TheoremM Unit := do
  let mctx ← getMCtx
  let mvars : List MVarId := (mctx.decls.toList.map (·.1))
  for mvar in mvars do
    if ← correctLocalVarNames mvar then
      continue
    else
      let _ ← renameLocalVarNames mvar
  setMVarsUserNames

def renameGoals : TheoremM Unit := do
  let mut new_goals := []
  let goals ← getGoals
  for goal in goals do
    if ← correctLocalVarNames goal then
      new_goals := goal :: new_goals
    else
      new_goals := (← renameLocalVarNames goal) :: new_goals
  setGoals new_goals.reverse
  setMVarsUserNames

/-- Lift a `TacticM` action into `M`. -/
@[inline] def liftTactic {α} (x : TacticM α) : TheoremM α := do
  liftGoals
  x

instance : MonadLift TacticM TheoremM where
  monadLift x := liftTactic x

-- TODO check that the main goal is `Prop`
def createThm : TacticM MVarId := do
  let mvarId ← getMainGoal
  -- the type is `Prop`
  let type : Expr := Expr.sort Level.zero
  let tag  : Name := `thm
  let newMVarE ← mkFreshExprSyntheticOpaqueMVar type tag
  let newMVar := newMVarE.mvarId!
  -- we assign the theorem with the main goal which should also be `Prop`. This way we can print the progress
  -- by printing the theorem mvar.
  newMVar.assign (mkMVar mvarId)
  return newMVar

def createContext : TacticM TheoremM.Context := do
  -- to avoid a bug. the repl produces a few meta variables which we might reproduce here and avoid name clashes for relevant meta variables.
  let x : Expr ← mkFreshExprSyntheticOpaqueMVar (Expr.sort .zero) `ignore
  let x : Expr ← mkFreshExprSyntheticOpaqueMVar x `ignore
  let x : Expr ← mkFreshExprSyntheticOpaqueMVar x `ignore
  let x : Expr ← mkFreshExprSyntheticOpaqueMVar x `ignore
  let _ := x
  -- Run your monad with the new goal in its context
  let ctx : TheoremM.Context := {}
  return ctx

def createState : TacticM TheoremM.State := do
  let thm ← createThm
  return ⟨thm, {}, 0, []⟩

/- copied Lean.Meta.withLocalContextImp -/
private def withLocalContextImp (lctx : LocalContext) (localInsts : LocalInstances) (x : MetaM α) : MetaM α := do
  withReader (fun ctx => { ctx with lctx := lctx, localInstances := localInsts }) do
    x


def addFVarToGlobalCtx (val type : Expr) : TheoremM (FVarId × MVarId) := do
  -- add the variable to the global context
  let thmE : Expr ← mkFreshExprSyntheticOpaqueMVar (Expr.sort .zero) `thm
  let thmMVarId := thmE.mvarId!
  let (fvarId, new_thm_mvarid) ← thmMVarId.note (← newHypName) val type
  let some e ← getExprMVarAssignment? (← getTheorem)
    | throwError "theorem is not assigned"
  new_thm_mvarid.assign e
  setTheorem new_thm_mvarid
  liftGoals
  return (fvarId, new_thm_mvarid)


/--
Adds a variable to the global context. we add a goal for the type of the new variable.
We do not expect a proof for the new variable. This is cheating!
At the end of the theorem generation, the variable will be given as a hypotheses.
Returns the type of the variable.
-/
def addVariable (u? : Option Level := none) (type? : Option Expr := none) : TheoremM (FVarId × MVarId) := do
  (← getTheorem).withContext do
    -- Universe metavariable ?u, so type lives in Sort ?u
    -- if `u?` is given, we use it for `u`. Otherwise we create a new lmvar.
    let u : Level ← match u? with
      | some u => pure u
      | none =>
        match type? with
        | some type => getLevel type
        | none => mkFreshLevelMVar
    let uE : Expr := mkSort u
    -- Type metavariable ?T : Sort ?u
    -- if `type?` is given, we use it for `type`. Otherwise we create a new mvar.
    let type : Expr ← match type? with
      | some type => pure type
      | none =>
        let mvar ← mkFreshExprMVar uE
        pushGoal mvar.mvarId!
        pure mvar
    let val : Expr ← mkSorry type true
    addFVarToGlobalCtx val type

/--
Adds a proposition to the global context. we add a goal for the type of the proposition.
We do not expect a proof for the new variable. This is cheating!
At the end of the theorem generation, the proposition will be given as a hypotheses.
-/
def addPropVariable : TheoremM Unit := do
  discard <| addVariable (some 0)

/--
Adds a type of type `Type` and `n` elements of this type to the global context. This is cheating!
At the end of the theorem generation, the variables will be given as a hypotheses.
-/
def addTypeVariable (n : Nat) : TheoremM Unit := do
  let mut thm  : MVarId := default
  let mut type : FVarId := default
  (type, thm) ← addVariable (some 1) (some (Expr.sort 1))
  for _ in [: n] do
    thm ← thm.withContext do
      let (_, thm) ← addVariable none (Expr.fvar type)
      return thm

/--
Adds a function `a → b` aswell as `a` and `b` to the global context. This is cheating!
At the end of the theorem generation, the variable will be given as a hypotheses.
It will open goals for the type of `a` and `b`.
-/
def addFunctionVariable : TheoremM Unit := do
  let (a, thm) ← addVariable
  thm.withContext do
    let (b, thm) ← addVariable
    thm.withContext do
      discard <| addFVarToGlobalCtx
        (type := ← mkArrow (← a.getType) (← b.getType))
        (val := .lam default (← a.getType) (.fvar b) default)

/--
This adds a variable of the type of the main goal to the gloabl context and uses it to close the goal.
This is cheating!
At the end of the theorem generation, the variable will be given as a hypotheses.
-/
def closeGoal : TheoremM Unit := do
  let goal ← getMainTarget
  discard <| addVariable (type? := some goal)
  evalTactic (← `(tactic| assumption))

def rename : TheoremM Unit := do
  -- TheoremM.renameGoals
  renameMVars
  setLevelNames

def ppTheorem : TheoremM Format := do
  let depth := pp.syntaxDepth.get (← getOptions)
  let s ← getThe TheoremM.State
  let n_goals := (← getGoals).length
  let thm := s.thm
  let some val ← getExprMVarAssignment? thm
    | throwError "theorem not assigned. Therefore it can not be printed"
  thm.withContext do
    let val ← instantiateMVars val
    let valFmt ← ppExpr val
    let thmFmt ← PrettyPrinter.ppGoal thm
    -- let failedTactics ← s.failedTactics.mapM (Lean.PrettyPrinter.My.ppTactic ·)
    -- let failedTacticsFmt : Format := Format.joinSep failedTactics (sep ++ withDepth depth "<failed_tactic>" ++ sep)
    return withDepth depth "⟨n_goals⟩" ++ sep ++ Syntax.repr (depth + 1) (My.digits_stx n_goals) ++ sep ++
      withDepth depth "⟨theorem_start⟩" ++ sep ++ thmFmt ++ sep ++
      withDepth depth "⟨theorem_value⟩" ++ sep ++
      valFmt ++ sep ++ withDepth depth "⟨theorem_end⟩" ++ sep -- ++
      -- withDepth depth "⟨failedTactics_start⟩" ++ sep ++ failedTacticsFmt ++ sep ++
      -- withDepth depth "⟨failedTactics_end⟩" ++ sep

end TheoremM
