import Lean
import Mathlib.Lean.Meta.Simp
import DAG.Basic
import DAG.Isomorphism
import InfoGeometry.Canonical.GeneratedFlow
import InfoGeometry.Canonical.SpineAttributes

open Lean Meta
open InfoGeometry.Canonical

namespace DAG

def liftNaturalityNormalizationLemmas : List Name :=
  [ ``InfoGeometry.Canonical.LogGenerator.generate_eq_along
  , ``InfoGeometry.Canonical.LogGenerator.generate_apply
  , ``InfoGeometry.Canonical.GeneratedFlow.along_apply
  ]

def taggedLiftDecls (env : Environment) (ns? : Option Name := none) : Array Name :=
  let decls := env.constants.fold (init := #[]) fun acc declName _ =>
    if let some ns := ns? then
      if !ns.isPrefixOf declName then
        acc
      else if isSpineFunctorLift env declName then
        acc.push declName
      else
        acc
    else if isSpineFunctorLift env declName then
      acc.push declName
    else
      acc
  decls.qsort fun a b => a.toString < b.toString

structure LiftSeed where
  theoremName : Name
  headLiftMentions : Array Name
  liftMentions : Array Name
  rawLhs : String
  rawRhs : String
  normLhs : String
  normRhs : String
  rawHashEq : Bool
  normHashEq : Bool
  normDefEq : Bool
  normalizationError? : Option String := none

private def ppExprString (e : Expr) : MetaM String := do
  pure (← ppExpr e).pretty

private def liftMentionsOf (liftSet : Std.HashSet Name) (e : Expr) : Array Name :=
  let names := DAG.collectExprConsts e |>.toList.toArray
  (names.filter fun n => liftSet.contains n).qsort fun a b => a.toString < b.toString

private def dedupNames (names : Array Name) : Array Name :=
  let seen := names.foldl (init := ({} : Std.HashSet Name)) fun acc n => acc.insert n
  seen.toArray.qsort fun a b => a.toString < b.toString

private def headConstName? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | .proj s _ _ => some s
  | _ => none

private def headLiftMentionsOf (liftSet : Std.HashSet Name) (lhs rhs : Expr) : Array Name :=
  let heads :=
    #[headConstName? lhs, headConstName? rhs].filterMap id |>.filter fun n => liftSet.contains n
  dedupNames heads

private def normalizeEqSides (lhs rhs : Expr) : MetaM (Expr × Expr × Option String) := do
  let lhsWhnf ← whnf lhs
  let rhsWhnf ← whnf rhs
  try
    let lhs' := (← Lean.Meta.simpOnlyNames liftNaturalityNormalizationLemmas lhsWhnf).expr
    let rhs' := (← Lean.Meta.simpOnlyNames liftNaturalityNormalizationLemmas rhsWhnf).expr
    pure (lhs', rhs', none)
  catch _ =>
    pure (lhsWhnf, rhsWhnf, some "simp normalization fell back to whnf")

private def isTheoremConstant (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ => true
  | _ => false

private def mkLiftSeed? (liftSet : Std.HashSet Name) (declName : Name) (ci : ConstantInfo) :
    MetaM (Option LiftSeed) := do
  let seed? ← observing? <| forallTelescope ci.type fun _ body => do
    let bodyWhnf ← whnf body
    let some (_, lhs, rhs) := body.eq? <|> bodyWhnf.eq? | failure
    let headLiftMentions := headLiftMentionsOf liftSet lhs rhs
    if headLiftMentions.isEmpty then
      failure
    let rawLiftMentions :=
      let mentions :=
        liftMentionsOf liftSet lhs ++
        liftMentionsOf liftSet rhs ++
        liftMentionsOf liftSet ci.type
      dedupNames mentions
    if rawLiftMentions.isEmpty then
      failure
    let lhsRawStr ← ppExprString lhs
    let rhsRawStr ← ppExprString rhs
    let rawHashEq := DAG.computeStructuralHash lhs == DAG.computeStructuralHash rhs
    let (lhsNorm, rhsNorm, normalizationError?) ← normalizeEqSides lhs rhs
    let lhsNormStr ← ppExprString lhsNorm
    let rhsNormStr ← ppExprString rhsNorm
    let normHashEq := DAG.computeStructuralHash lhsNorm == DAG.computeStructuralHash rhsNorm
    let normDefEq ← withNewMCtxDepth <| isDefEq lhsNorm rhsNorm
    pure
      { theoremName := declName
        headLiftMentions := headLiftMentions
        liftMentions := rawLiftMentions
        rawLhs := lhsRawStr
        rawRhs := rhsRawStr
        normLhs := lhsNormStr
        normRhs := rhsNormStr
        rawHashEq := rawHashEq
        normHashEq := normHashEq
        normDefEq := normDefEq
        normalizationError? := normalizationError?
      }
  pure seed?

def collectLiftSeeds (env : Environment) (nsPrefix : Name) : MetaM (Array LiftSeed × Array Name) := do
  let lifts := taggedLiftDecls env (some nsPrefix)
  let mut liftSet : Std.HashSet Name := {}
  for liftName in lifts do
    liftSet := liftSet.insert liftName
  let mut seeds := #[]
  for (declName, ci) in env.constants do
    if !nsPrefix.isPrefixOf declName then
      continue
    if !isTheoremConstant ci then
      continue
    if (liftMentionsOf liftSet ci.type).isEmpty then
      continue
    match ← mkLiftSeed? liftSet declName ci with
    | some seed => seeds := seeds.push seed
    | none => pure ()
  pure (seeds.qsort fun a b => a.theoremName.toString < b.theoremName.toString, lifts)

end DAG
