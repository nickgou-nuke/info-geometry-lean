import Lean

open Lean

namespace InfoGeometry.Meta

/-- Head shape of an elaborated theorem proof or definition value. -/
inductive ProofHeadShape where
  | exactConst (target : Name)
  | exactApp (head : Name) (nargs : Nat)
  | rfl
  | trivial
  | lambda
  | other
  deriving Repr, Inhabited, DecidableEq, BEq

/-- Outermost statement shape after stripping leading binders. -/
inductive StatementShape where
  | eq
  | iff
  | forallEq
  | forallIff
  | prop
  | other
  deriving Repr, Inhabited, DecidableEq, BEq

/-- First-pass thin-surface classification over an elaborated declaration. -/
inductive ThinSurfaceKind where
  | wrapper
  | reprojection
  deriving Repr, Inhabited, DecidableEq, BEq

/-- Semantic proof-shape report for admission and anti-vacuity checks. -/
structure ProofShapeReport where
  proofHead : ProofHeadShape
  statementShape : StatementShape
  thinSurface? : Option ThinSurfaceKind := none
  deriving Repr, Inhabited

def ProofHeadShape.asString : ProofHeadShape → String
  | .exactConst target => s!"exactConst:{target}"
  | .exactApp head nargs => s!"exactApp:{head}/{nargs}"
  | .rfl => "rfl"
  | .trivial => "trivial"
  | .lambda => "lambda"
  | .other => "other"

def StatementShape.asString : StatementShape → String
  | .eq => "eq"
  | .iff => "iff"
  | .forallEq => "forallEq"
  | .forallIff => "forallIff"
  | .prop => "prop"
  | .other => "other"

def ThinSurfaceKind.asString : ThinSurfaceKind → String
  | .wrapper => "wrapper"
  | .reprojection => "reprojection"

instance : ToJson ProofHeadShape where
  toJson s := Json.str s.asString

instance : ToJson StatementShape where
  toJson s := Json.str s.asString

instance : ToJson ThinSurfaceKind where
  toJson s := Json.str s.asString

private def stripLambdas : Expr → Expr
  | .mdata _ body => stripLambdas body
  | .lam _ _ body _ => stripLambdas body
  | e => e

private def stripForalls : Expr → Expr
  | .mdata _ body => stripForalls body
  | .forallE _ _ body _ => stripForalls body
  | e => e

def classifyProofHead (valueExpr : Expr) : ProofHeadShape :=
  let v := stripLambdas valueExpr
  if v.isConst then
    .exactConst v.constName!
  else if v.isAppOfArity ``Eq.refl 2 then
    .rfl
  else if v.isAppOfArity ``rfl 2 then
    .rfl
  else if v.isConstOf ``True.intro then
    .trivial
  else if v.isApp then
    let f := v.getAppFn
    if f.isConst then
      .exactApp f.constName! v.getAppNumArgs
    else
      .other
  else if v.isLambda then
    .lambda
  else
    .other

def classifyStatementShape (typeExpr : Expr) : StatementShape :=
  let inner := stripForalls typeExpr
  if inner.isAppOfArity ``Eq 3 then
    if typeExpr.isForall then .forallEq else .eq
  else if inner.isAppOfArity ``Iff 2 then
    if typeExpr.isForall then .forallIff else .iff
  else
    .prop

def ProofHeadShape.isForwarding : ProofHeadShape → Bool
  | .exactConst _ => true
  | .exactApp _ nargs => nargs ≤ 4
  | .rfl => true
  | .trivial => true
  | _ => false

def ProofHeadShape.forwardTarget? : ProofHeadShape → Option Name
  | .exactConst target => some target
  | .exactApp head _ => some head
  | _ => none

def classifyThinSurface
    (proofHead : ProofHeadShape)
    (statementShape : StatementShape) : Option ThinSurfaceKind :=
  if !proofHead.isForwarding then
    none
  else
    match statementShape with
    | .eq | .forallEq | .iff | .forallIff => some .reprojection
    | .prop => some .wrapper
    | .other => none

def analyzeProofShape (typeExpr valueExpr : Expr) : ProofShapeReport :=
  let proofHead := classifyProofHead valueExpr
  let statementShape := classifyStatementShape typeExpr
  { proofHead, statementShape
    thinSurface? := classifyThinSurface proofHead statementShape }

end InfoGeometry.Meta
