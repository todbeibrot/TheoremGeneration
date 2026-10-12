import Lean
import REPL.PP.ppGoal

open Lean

namespace Lean.PrettyPrinter
namespace My

def ppCategory (_ : Name) (stx : Syntax) : CoreM Format := do
  let opts ← getOptions
  let stx := (sanitizeSyntax stx).run' { options := opts }
  let depth := pp.syntaxDepth.get opts
  return Syntax.repr depth stx

def ppTerm (stx : Term) : CoreM Format := ppCategory `term stx

def ppUsing (e : Expr) (delab : Expr → MetaM Term) : MetaM Format := do
  let lctx := (← getLCtx).sanitizeNames.run' { options := (← getOptions) }
  Meta.withLCtx' lctx do
    ppTerm (← delab e)

def ppExpr (e : Expr) : MetaM Format := do
  ppUsing e delab

/-- Return a `fmt` representing pretty-printed `e` together with a map from tags in `fmt`
to `Elab.Info` nodes produced by the delaborator at various subexpressions of `e`. -/
def ppExprWithInfos (e : Expr) (optsPerPos : Delaborator.OptionsPerPos := {}) (delab := Delaborator.delab)
    : MetaM FormatWithInfos := do
  let lctx := (← getLCtx).sanitizeNames.run' { options := (← getOptions) }
  Meta.withLCtx' lctx do
    let (stx, infos) ← delabCore e optsPerPos delab
    let fmt ← ppTerm stx
    return ⟨fmt, infos⟩

open Delaborator in
def ppConstNameWithInfos (constName : Name) : MetaM FormatWithInfos := do
  if let some info := (← getEnv).find? constName then
    let delab := withOptionAtCurrPos `pp.tagAppFns true <| delabConst
    PrettyPrinter.ppExprWithInfos (delab := delab) (.const constName <| info.levelParams.map mkLevelParam)
  else
    -- Still, let's sanitize the name.
    let stx := mkIdent constName
    let stx := (sanitizeSyntax stx).run' { options := (← getOptions) }
    formatCategory `term stx

def ppExprLegacy (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : IO Format :=
  Prod.fst <$> ((withOptions (fun _ => opts) <| ppExpr e).run' { lctx := lctx } { mctx := mctx }).toIO
    { fileName := "<PrettyPrinter>", fileMap := default }
    { env := env }

def ppTactic (stx : TSyntax `tactic) : CoreM Format := ppCategory `tactic stx

def ppCommand (stx : Syntax.Command) : CoreM Format := ppCategory `command stx

def ppModule (stx : TSyntax ``Parser.Module.module) : CoreM Format := do
  parenthesize Lean.Parser.Module.module.parenthesizer stx >>= format Lean.Parser.Module.module.formatter

open Delaborator in
/-- Pretty-prints a declaration `c` as `c.{<levels>} <params> : <type>`. -/
def ppSignature (c : Name) : MetaM FormatWithInfos := do
  let decl ← getConstInfo c
  let e := Expr.const c (decl.levelParams.map mkLevelParam)
  if pp.raw.get (← getOptions) then
    return s!"{e} : {decl.type}"
  else
    let (stx, infos) ← delabCore e (delab := delabConstWithSignature)
    return ⟨← ppTerm ⟨stx⟩, infos⟩  -- HACK: not a term

private partial def noContext : MessageData → MessageData
  | MessageData.withContext _   msg => noContext msg
  | MessageData.withNamingContext ctx msg => MessageData.withNamingContext ctx (noContext msg)
  | MessageData.nest n msg => MessageData.nest n (noContext msg)
  | MessageData.group msg  => MessageData.group (noContext msg)
  | MessageData.compose msg₁ msg₂ => MessageData.compose (noContext msg₁) (noContext msg₂)
  | MessageData.tagged tag msg => MessageData.tagged tag (noContext msg)
  | MessageData.trace data header children =>
    MessageData.trace data (noContext header) (children.map noContext)
  | msg => msg

-- strip context (including environments with registered pretty printers) to prevent infinite recursion when pretty printing pretty printer error
private def withoutContext {m} [MonadExcept Exception m] (x : m α) : m α :=
  tryCatch x fun
    | Exception.error ref msg => throw <| Exception.error ref (noContext msg)
    | ex                      => throw ex

initialize
  ppFnsRef.set {
    ppExprWithInfos := fun ctx e => ctx.runMetaM <| withoutContext <| ppExprWithInfos e
    ppConstNameWithInfos := fun ctx n => ctx.runMetaM <| withoutContext <| ppConstNameWithInfos n
    ppTerm := fun ctx stx => ctx.runCoreM <| withoutContext <| ppTerm stx
    ppLevel := fun ctx l => return l.format (mvars := getPPMVarsLevels ctx.opts)
    ppGoal := fun ctx mvarId => ctx.runMetaM <| withoutContext <| PrettyPrinter.ppGoal mvarId
  }
