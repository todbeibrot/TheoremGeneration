import Lean

/- This file is only for debugging. We introduce here some functionality to print more detailed informations
  while running the repl. In particular the states of the monads building the fundament of the tactic monad.
  This includes all metavariables, assignments of metavariables, ... -/

open Lean Meta

def Lean.PersistentHashMap.size {α β} [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β) : Nat :=
  (PersistentHashMap.toList map).length

namespace CtxDebug

def getPPContext : MetaM Lean.PPContext := do
  let env ← getEnv
  let opts ← getOptions
  let mctx ← getMCtx
  let lctx ← getLCtx
  return {
    env           := env
    mctx          := mctx
    lctx          := lctx
    opts          := opts
    currNamespace := Name.anonymous
    openDecls     := []
  }

/-- Pretty-print an expression. -/
private def ppE (e : Expr) : MetaM Format :=
  ppExpr e

/-- Pretty-print a universe level. -/
private def ppL (u : Level) : MetaM Format := do
  ppLevel (← getPPContext) u

/-- Return a `Format` for a `cdecl` local declaration. -/
private def fmtCDecl
  (index : Nat) (fvarId : FVarId) (userName : Name)
  (type : Expr) (bi : BinderInfo) (kind : LocalDeclKind) : MetaM Format := do
  let ty ← ppExpr type
  return Format.joinSep
    [ f!"- fvarId: {fvarId.name}"
    , f!"  userName: {userName}"
    , f!"  binderInfo: {repr bi}"
    , f!"  kind: {repr kind}"
    , f!"  index: {index}"
    , f!"  type: {ty}"
    ] Format.line

/-- Return a `Format` for an `ldecl` local declaration. -/
private def fmtLDecl
  (index : Nat) (fvarId : FVarId) (userName : Name)
  (type value : Expr) (nondep : Bool) (kind : LocalDeclKind) : MetaM Format := do
  let ty ← ppExpr type
  let val ← ppExpr value
  return Format.joinSep
    [ f!"- fvarId: {fvarId.name}"
    , f!"  userName: {userName}"
    , f!"  kind: {repr kind}"
    , f!"  index: {index}"
    , f!"  nondep: {nondep}"
    , f!"  type: {ty}"
    , f!"  value: {val}"
    ] Format.line

/-- Dispatcher for `LocalDecl`, returning a `Format`. -/
private def fmtLocalDecl (d : LocalDecl) : MetaM Format :=
  match d with
  | .cdecl idx fvarId userName type bi kind =>
      fmtCDecl idx fvarId userName type bi kind
  | .ldecl idx fvarId userName type value nondep kind =>
      fmtLDecl idx fvarId userName type value nondep kind

/-- Return a `Format` for one `MetavarDecl` with many details. -/
private def fmtMetavarDecl (id : MVarId) (d : MetavarDecl) : MetaM Format := do
  let ty ← ppExpr d.type
  let header :=
    Format.joinSep
      [ f!"- mvarId: {id.name}"
      , f!"  userName: {d.userName}"
      , f!"  kind: {repr d.kind}"
      , f!"  index: {d.index}"
      , f!"  depth: {d.depth}"
      , f!"  type: {ty}"
      , f!"  localInstances.size: {d.localInstances.size}"
      , f!"  ---- local context ----"
      ] Format.line

  let mut declLines : Array Format := #[]
  for localDecl in d.lctx do
    declLines := declLines.push (← fmtLocalDecl localDecl)

  let declsFmt :=
    if declLines.isEmpty then
      f!"  (empty)"
    else
      Format.joinSep declLines.toList Format.line

  return Format.joinSep [header, declsFmt] Format.line

/--
Return one `Format` containing:
- ambient `LocalContext`
- full `MetavarContext` summary
- all `MetavarDecl`s
- `eAssignment`, `lAssignment`, `dAssignment`
-/
def print_ctx : MetaM Format := do
  let lctx ← getLCtx
  let mctx ← getMCtx

  let mut out : Array Format := #[]

  out := out.push f!"==================== LocalContext (ambient Meta.Context.lctx) ===================="
  for d in lctx do
    out := out.push (← fmtLocalDecl d)

  out := out.push f!"==================== MetavarContext (Meta.State.mctx) ===================="
  out := out.push f!"depth: {mctx.depth}"
  out := out.push f!"levelAssignDepth: {mctx.levelAssignDepth}"
  out := out.push f!"levels: {mctx.lDepth.toList.map (fun (x, y) => (x.name, y))}"
  out := out.push f!"mvarCounter: {mctx.mvarCounter}"
  out := out.push f!"decls.size: {mctx.decls.size}"
  out := out.push f!"userNames: {mctx.userNames.toList.map (fun (x, _) => x)}"
  out := out.push f!"eAssignment.size: {mctx.eAssignment.size}"
  out := out.push f!"lAssignment.size: {mctx.lAssignment.size}"
  out := out.push f!"dAssignment.size: {mctx.dAssignment.size}"

  out := out.push f!"-------------------- MetavarDecls --------------------"
  for (id, d) in mctx.decls do
    out := out.push (← fmtMetavarDecl id d)

  out := out.push f!"-------------------- Expr assignments (eAssignment) --------------------"
  for (id, e) in mctx.eAssignment do
    let efmt ← ppE e
    out := out.push f!"- {id.name} := {efmt}"

  out := out.push f!"-------------------- Level assignments (lAssignment) --------------------"
  for (id, u) in mctx.lAssignment do
    let ufmt ← ppL u
    out := out.push f!"- {id.name} := {ufmt}"

  out := out.push f!"-------------------- Delayed assignments (dAssignment) --------------------"
  for (id, da) in mctx.dAssignment do
    out := out.push f!"- {id.name} := {repr da.fvars} + {repr da.mvarIdPending}"

  out := out.push f!"-------------------- End --------------------"

  return Format.joinSep out.toList Format.line

end CtxDebug
