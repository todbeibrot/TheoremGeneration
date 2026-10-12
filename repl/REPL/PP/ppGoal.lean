import Lean

import REPL.PP.ppOptions

open Lean Meta


register_option pp.syntaxDepth : Nat := {
  defValue := 0
  descr    := "(pretty printer) does notate the current depth in the printed syntax tree. \
      If we add a syntax tree to the output, we start at this depth"
}

def SyntaxDepth (depth : Nat) (opts : Options) : Options :=
  pp.syntaxDepth.set opts depth

def withSyntaxDepth {α} (depth : Nat) (act : CoreM α) : CoreM α := do
  withOptions (SyntaxDepth depth) act

def withSyntaxDepth' {α} (depth : Nat) (act : MetaM α) : MetaM α := do
  withOptions (SyntaxDepth depth) act

def withIncreasedSyntaxDepth {α} (act : CoreM α) : CoreM α := do
  let depth := pp.syntaxDepth.get (← getOptions)
  withSyntaxDepth (depth + 1) act

def withIncreasedSyntaxDepth' {α} (act : MetaM α) : MetaM α := do
  let depth := pp.syntaxDepth.get (← getOptions)
  withSyntaxDepth' (depth + 1) act

-- Hopefully these symbols are never used in Lean
def sep : Format := "\t"
def depthSep : Format := "\u001E"

def withDepth (depth : Nat) (f : Format) : Format :=
  f ++ depthSep ++ toString depth

def withDepthM (f : Format) : MetaM Format := do
  let depth := pp.syntaxDepth.get (← getOptions)
  return f ++ depthSep ++ toString depth

partial def Syntax.repr (depth : Nat) : Lean.Syntax → Format
| .missing => .nil
| .node _ kind args =>
    if args.size == 0 then withDepth depth kind.toString else
      withDepth depth kind.toString ++ sep ++ Std.Format.joinSep (args.map (Syntax.repr (depth + 1))).toList sep
| .atom _ val => withDepth depth val
| .ident _ _ val _ => withDepth depth val.toString

def variable_prefix : MetaM Format := do
  withDepthM "<variable>"

namespace PrettyPrinter

def Lean.ppExprWithInfos (ctx : PPContext) (e : Expr) : BaseIO FormatWithInfos := do
  if pp.raw.get ctx.opts then
    let e := instantiateMVarsCore ctx.mctx e |>.1
    return format (toString e)
  else
    match (← ppExt.getState ctx.env |>.ppExprWithInfos ctx e |>.toBaseIO) with
    | .ok fmt => return fmt
    | .error ex =>
      if pp.rawOnError.get ctx.opts then
        pure f!"[Error pretty printing expression: {ex}. Falling back to raw printer.]{Format.line}{e}"
      else
        pure f!"failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)"

/-- Pretty-print the given expression. -/
def ppExprWithInfos (e : Expr) : MetaM FormatWithInfos := do
  let ctxCore  ← readThe Core.Context
  Lean.ppExprWithInfos { env := (← getEnv), mctx := (← getMCtx), lctx := (← getLCtx), opts := (← getOptions), currNamespace := ctxCore.currNamespace, openDecls := ctxCore.openDecls } e

def ppExpr (e : Expr) : MetaM Format := do
  return (← withDepthM "<expr>") ++ sep ++ (← withIncreasedSyntaxDepth' do (·.fmt) <$> ppExprWithInfos e)

def ppGoal (mvarId : MVarId) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId with
  | none          => return "unknown goal"
  | some mvarDecl =>
    let ppAuxDecls     := pp.auxDecls.get (← getOptions)
    let ppImplDetailHyps := pp.implementationDetailHyps.get (← getOptions)
    let depth := pp.syntaxDepth.get (← getOptions)
    -- Heuristic: synthetic opaque metavariables are only used by tactics,
    -- and tactics should always be creating synthetic opaque metavariables for new goals.
    let tactic         := mvarDecl.kind.isSyntheticOpaque
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    withLCtx lctx mvarDecl.localInstances do
      -- The following two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : MetaM Format := do
        if ids.isEmpty then
          return fmt
        else
          let v_prefix : Format ← variable_prefix
          withIncreasedSyntaxDepth' do
            let fmt := fmt ++ sep ++ v_prefix
            match type? with
            | none      => return fmt
            | some type =>
              let depth := pp.syntaxDepth.get (← getOptions)
              let typeFmt ← ppExpr type
              return fmt ++ sep ++
                Format.joinSep ((ids.reverse).map (fun id => withDepth depth (format id))) sep ++ sep ++
                withDepth depth ":" ++ sep ++ typeFmt
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (fmt : Format) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × Format) := do
        match localDecl with
        | .cdecl _ _ varName type ..
        | .ldecl _ _ varName type (nondep := true) .. =>
          let varName := varName.simpMacroScopes
          let type ← instantiateMVars type
          if prevType? == none || prevType? == some type then
            return (varName :: varNames, some type, fmt)
          else do
            let fmt ← pushPending varNames prevType? fmt
            return ([varName], some type, fmt)
        | .ldecl _ _ varName type val (nondep := false) .. => do
          let varName := varName.simpMacroScopes
          let fmt ← pushPending varNames prevType? fmt
          withIncreasedSyntaxDepth' do
            let type ← instantiateMVars type
            let typeFmt ← ppExpr type
            let mut fmtElem := withDepth depth (format varName) ++ sep ++ withDepth depth ":" ++ sep ++ typeFmt
            let val ← instantiateMVars val
            if ← ppGoal.shouldShowLetValue tactic val then
              let valFmt ← ppExpr val
              fmtElem := fmtElem ++ sep ++ withDepth depth ":=" ++ sep ++ valFmt
            else
              fmtElem := fmtElem ++ sep ++ withDepth depth ":=⋯"
            let fmt := fmt ++ sep ++ fmtElem
            return ([], none, fmt)
      let (varNames, type?, fmt) ←
        lctx.foldlM (init := ([], none, Format.nil)) fun (varNames, prevType?, fmt) (localDecl : LocalDecl) =>
          if !ppAuxDecls && localDecl.isAuxDecl || !ppImplDetailHyps && localDecl.isImplementationDetail then
            return (varNames, prevType?, fmt)
          else
            ppVars varNames prevType? fmt localDecl
      let fmt ← pushPending varNames type? fmt
      let typeFmt ← withIncreasedSyntaxDepth' do ppExpr (← instantiateMVars mvarDecl.type)
      let fmt := fmt ++ sep ++ withDepth depth (getGoalPrefix mvarDecl) ++ sep ++ typeFmt
      match mvarDecl.userName with
      | Name.anonymous => return fmt
      | name           => return withDepth depth "case" ++ sep ++ withDepth depth (format name.eraseMacroScopes) ++ sep ++ fmt

def ppGoals (goals : List MVarId) : MetaM Format := do
  withOptions ppOptions do
    let depth := pp.syntaxDepth.get (← getOptions)
    let fmts ← withIncreasedSyntaxDepth' do goals.mapM ppGoal
    return Format.joinSep fmts (sep ++ withDepth depth "<goal>" ++ sep)

end PrettyPrinter
