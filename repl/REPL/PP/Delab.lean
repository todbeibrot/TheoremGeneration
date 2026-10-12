import Lean

/- Workspace. Dont take it serious. -/

open Lean Elab Command Term Meta PrettyPrinter Delaborator SubExpr Parser
open TSyntax.Compat

namespace My

@[delab fvar]
def delabFVar : Delab := do
  let Expr.fvar fvarId ← getExpr | unreachable!
  try
    let l ← fvarId.getDecl
    maybeAddBlockImplicit (mkIdent l.userName)
  catch _ =>
    -- loose free variable, use internal name
    maybeAddBlockImplicit <| mkIdent (fvarId.name.replacePrefix `_uniq `_fvar)

def delabMVarAux (m : MVarId) : DelabM Term := do
  let mkMVarPlaceholder : DelabM Term := `(?_)
  let mkMVar (n : Name) : DelabM Term := `(?$(mkIdent n))
  withTypeAscription (cond := ← getPPOption getPPMVarsWithType) do
    if ← getPPOption getPPMVars then
      if let some decl ← m.findDecl? then
        match decl.userName with
        | .anonymous =>
          if ← getPPOption getPPMVarsAnonymous then
            mkMVar <| Name.num `m (decl.index + 1)
          else
            mkMVarPlaceholder
        | n => mkMVar n
      else
        -- Undefined mvar, use internal name
        mkMVar <| m.name.replacePrefix `_uniq `_mvar
    else
      mkMVarPlaceholder

@[delab mvar]
def delabMVar : Delab := do
  let Expr.mvar n ← getExpr | unreachable!
  delabMVarAux n

@[delab sort]
def delabSort : Delab := do
  let Expr.sort l ← getExpr | unreachable!
  match l with
  | Level.zero => `(Prop)
  | Level.succ .zero => `(Type)
  | _ =>
    let mvars ← getPPOption getPPMVarsLevels
    match l.dec with
    | some l' => `(Type $(Level.quote l' (prec := max_prec) (mvars := mvars)))
    | none    => `(Sort $(Level.quote l (prec := max_prec) (mvars := mvars)))

@[delab app]
def delabDelayedAssignedMVar : Delab := whenNotPPOption getPPMVarsDelayed do
  let .mvar mvarId := (← getExpr).getAppFn | failure
  let some decl ← getDelayedMVarAssignment? mvarId | failure
  withOverApp decl.fvars.size do
    let args := (← getExpr).getAppArgs
    -- Only delaborate using decl.mvarIdPending if the delayed mvar is applied to fvars
    guard <| args.all Expr.isFVar
    delabMVarAux decl.mvarIdPending


/-- Split a Nat into decimal digits. `digits 0 = [0]`. -/
def digits (n : Nat) : Array Nat :=
  if n = 0 then
    #[0]
  else
    let rec go (n : Nat) (acc : List Nat) :=
      if n = 0 then acc
      else
        go (n / 10) ((n % 10) :: acc)
    ⟨go n []⟩

def digits_stx (n : Nat) : TSyntax numLitKind := mkNode numLitKind ((digits n).map
    (fun n => Syntax.atom SourceInfo.none <| toString n))


@[delab app.Char.ofNat]
def delabChar : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 1
  let .lit (.natVal n) := e.appArg! | failure
  let n_stx := digits_stx n
  let stx ← `(Char.ofNat $n_stx)
  return stx

/--
Core function that delaborates a natural number (an `OfNat.ofNat` literal).
-/
def delabOfNatCore (showType : Bool := false) : Delab := do
  let .app (.app (.app (.const ``OfNat.ofNat ..) _) (.lit (.natVal n))) _ ← getExpr | failure
  let stx ← annotateTermInfo <| digits_stx n
  if showType then
    let ty ← withNaryArg 0 delab
    `(($stx : $ty))
  else
    return stx

/--
Core function that delaborates a negative integer literal (a `Neg.neg` applied to `OfNat.ofNat`).
-/
def delabNegIntCore (showType : Bool := false) : Delab := do
  guard <| (← getExpr).isAppOfArity ``Neg.neg 3
  let n ← withAppArg delabOfNatCore
  let stx ← annotateTermInfo (← `(- $n))
  if showType then
    let ty ← withNaryArg 0 delab
    `(($stx : $ty))
  else
    return stx

/--
Core function that delaborates a rational literal that is the division of an integer literal
by a natural number literal.
The division must be homogeneous for it to count as a rational literal.
-/
def delabDivRatCore (showType : Bool := false) : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``HDiv.hDiv 6
  guard <| e.getArg! 0 == e.getArg! 1
  guard <| e.getArg! 0 == e.getArg! 2
  let p ← withAppFn <| withAppArg <| (delabOfNatCore <|> delabNegIntCore)
  let q ← withAppArg <| delabOfNatCore
  let stx ← annotateTermInfo (← `($p / $q))
  if showType then
    let ty ← withNaryArg 0 delab
    `(($stx : $ty))
  else
    return stx

/--
Delaborates an `OfNat.ofNat` literal.
`@OfNat.ofNat _ n _` ~> `n`.
-/
@[delab app.OfNat.ofNat]
def delabOfNat : Delab := do
  let showType ← getPPOption getPPNumericTypes
  whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions <| withOverApp 3 do
    delabOfNatCore (showType := ← pure showType <||> getPPOption getPPNumericTypes)

/--
Delaborates the negative of an `OfNat.ofNat` literal.
`-@OfNat.ofNat _ n _` ~> `-n`
-/
@[delab app.Neg.neg]
def delabNeg : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions do
  delabNegIntCore (showType := (← getPPOption getPPNumericTypes))

/--
Delaborates a rational number literal.
`@OfNat.ofNat _ n _ / @OfNat.ofNat _ m` ~> `n / m`
and `-@OfNat.ofNat _ n _ / @OfNat.ofNat _ m` ~> `-n / m`
-/
@[delab app.HDiv.hDiv]
def delabHDiv : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions do
  delabDivRatCore (showType := (← getPPOption getPPNumericTypes))

-- TODO
-- `@OfDecimal.ofDecimal _ _ m s e` ~> `m*10^(sign * e)` where `sign == 1` if `s = false` and `sign = -1` if `s = true`
@[delab app.OfScientific.ofScientific]
def delabOfScientific : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions <| withOverApp 5 do
  let expr ← getExpr
  guard <| expr.getAppNumArgs == 5
  let .lit (.natVal m) ← pure (expr.getArg! 2) | failure
  return digits_stx m

@[delab lit]
def delabLit : Delab := do
  let Expr.lit l ← getExpr | unreachable!
  match l with
  | Literal.natVal n =>
    if (← getPPOption getPPNatLit) || (← getPPOption getPPExplicit) then
      `(nat_lit $(digits_stx n))
    else
      return digits_stx n
  | Literal.strVal s => return mkNode strLitKind ((s.toList.map (fun c => c.toNat)).map digits_stx).toArray
