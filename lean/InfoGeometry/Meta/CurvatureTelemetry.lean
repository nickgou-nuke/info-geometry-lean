import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra
import DAG.Basic

open Lean Meta

namespace InfoGeometry.Meta

/--
Cheap integer-valued telemetry for gap curvature estimation.

This is not a kernel-level metric. It is failure-path search guidance for outer
agents deciding whether a gap looks local, structural, or prerequisite-heavy.
-/
structure CurvatureStats where
  targetWeight : Nat
  targetConstCount : Nat
  contextBindingCount : Nat
  contextConstUnionCount : Nat
  missingConstCount : Nat
  bestSharedConstCount : Nat
  bestSharedContextWeight : Nat
  exactSyntacticMatch : Bool
  bestContextName? : Option String
  deriving Repr, Inhabited

instance : ToJson CurvatureStats where
  toJson s :=
    let bestNameField :=
      match s.bestContextName? with
      | some name => [("bestContextName", Json.str name)]
      | none => []
    Json.mkObj <|
      [ ("targetWeight", toJson s.targetWeight)
      , ("targetConstCount", toJson s.targetConstCount)
      , ("contextBindingCount", toJson s.contextBindingCount)
      , ("contextConstUnionCount", toJson s.contextConstUnionCount)
      , ("missingConstCount", toJson s.missingConstCount)
      , ("bestSharedConstCount", toJson s.bestSharedConstCount)
      , ("bestSharedContextWeight", toJson s.bestSharedContextWeight)
      , ("exactSyntacticMatch", toJson s.exactSyntacticMatch)
      ] ++ bestNameField

/-- Structural AST weight used by the cheap curvature telemetry. -/
def exprWeight : Expr → Nat
  | .app f a => 1 + exprWeight f + exprWeight a
  | .lam _ d b _ => 1 + exprWeight d + exprWeight b
  | .forallE _ d b _ => 1 + exprWeight d + exprWeight b
  | .letE _ t v b _ => 1 + exprWeight t + exprWeight v + exprWeight b
  | .mdata _ b => 1 + exprWeight b
  | .proj _ _ b => 1 + exprWeight b
  | _ => 1

private def countNameSet (s : NameSet) : Nat :=
  s.toList.length

private def sharedConstCount (targetConsts ctxConsts : NameSet) : Nat :=
  targetConsts.toList.foldl (fun acc n =>
    if ctxConsts.contains n then acc + 1 else acc) 0

private def missingConstCount (targetConsts ctxUnion : NameSet) : Nat :=
  targetConsts.toList.foldl (fun acc n =>
    if ctxUnion.contains n then acc else acc + 1) 0

private def updateBest
    (bestShared bestWeight : Nat)
    (bestName? : Option String)
    (shared weight : Nat)
    (name : String) : Nat × Nat × Option String :=
  if shared > bestShared then
    (shared, weight, some name)
  else if shared = bestShared && weight > bestWeight then
    (shared, weight, some name)
  else
    (bestShared, bestWeight, bestName?)

/-- Compute cheap integer curvature telemetry for a target against a local context. -/
def extractCurvatureStats (target : Expr) (lctx : LocalContext) : MetaM CurvatureStats := do
  let target ← instantiateMVars target
  let targetConsts := DAG.collectExprConsts target
  let mut ctxUnion : NameSet := {}
  let mut contextBindingCount := 0
  let mut bestSharedConstCount := 0
  let mut bestSharedContextWeight := 0
  let mut bestContextName? : Option String := none
  let mut exactSyntacticMatch := false

  for localDecl in lctx do
    if !localDecl.isImplementationDetail then
      let localType ← instantiateMVars localDecl.type
      let localConsts := DAG.collectExprConsts localType
      let localWeight := exprWeight localType
      let shared := sharedConstCount targetConsts localConsts
      contextBindingCount := contextBindingCount + 1
      ctxUnion := ctxUnion.union localConsts
      let (shared', weight', name'?) :=
        updateBest bestSharedConstCount bestSharedContextWeight bestContextName?
          shared localWeight (toString localDecl.userName)
      bestSharedConstCount := shared'
      bestSharedContextWeight := weight'
      bestContextName? := name'?
      if localType == target then
        exactSyntacticMatch := true

  pure
    { targetWeight := exprWeight target
      targetConstCount := countNameSet targetConsts
      contextBindingCount := contextBindingCount
      contextConstUnionCount := countNameSet ctxUnion
      missingConstCount := missingConstCount targetConsts ctxUnion
      bestSharedConstCount := bestSharedConstCount
      bestSharedContextWeight := bestSharedContextWeight
      exactSyntacticMatch := exactSyntacticMatch
      bestContextName? := bestContextName?
    }

end InfoGeometry.Meta
