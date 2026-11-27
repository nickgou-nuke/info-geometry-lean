/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout
import InfoGeometry.Arithmetic.WeightedMangoldtSmoothing
import InfoGeometry.Arithmetic.SmoothedMangoldtMellin
import InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction
import InfoGeometry.Krein.Clifford
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Data.Json

/-!
# Native-pin trust audit for the arithmetic compatibility owners

The native CI lane checks this module at the root repository's Lean/Mathlib
pins. It audits the eleven changed native owners without importing the external
GRH proof. A run in the optional package checks compatibility at that package's
pins and does not certify the native environment.
Private/generated declarations are included, and transitive axiom dependencies
must lie in the three-foundation allowlist.
-/

#print axioms InfoGeometry.Arithmetic.RealDoubledDirichletReadout.scalarOp_eq_zero_iff
#print axioms InfoGeometry.Arithmetic.RealDoubledDirichletReadout.dirichletReadout_eq_zero_iff
#print axioms InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout.zetaReadout_eq_zero_iff_centeredXiReadout_zero
#print axioms InfoGeometry.Arithmetic.WeightedMangoldtSmoothing.centeredSmoothing_div_eq_centeredRemainder
#print axioms InfoGeometry.Arithmetic.WeightedMangoldtSmoothing.integerCenteredSqrtBound_iff_remainder
#print axioms InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction.riemannHypothesis_of_dirichletRightHalfPlane
#print axioms InfoGeometry.Krein.rot45Conj_symm_apply_apply

open Lean Elab Command

namespace InfoGeometry.GRHIntegration.NativeAxiomAudit

private def owners : Array Name := #[
  `InfoGeometry.Krein.Clifford,
  `InfoGeometry.Analysis.CenteredLogInterpolation,
  `InfoGeometry.Arithmetic.FiniteSmoothedMangoldt,
  `InfoGeometry.Arithmetic.SmoothedMangoldtReal,
  `InfoGeometry.Arithmetic.SmoothedMangoldtInterpolation,
  `InfoGeometry.Arithmetic.SmoothedMangoldtGrowth,
  `InfoGeometry.Arithmetic.SmoothedMangoldtMellin,
  `InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction,
  `InfoGeometry.Arithmetic.WeightedMangoldtSmoothing,
  `InfoGeometry.Arithmetic.RealDoubledDirichletReadout,
  `InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout]

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for owner in owners do
    unless modules.contains owner do
      throwError "GRH_AXIOM_AUDIT_FAILURE: missing imported owner {owner}"
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := modules[idx.toNat]? |
      throwError "GRH_AXIOM_AUDIT_FAILURE: invalid owner index for {name}"
    if owners.contains owner then names := names.push name
  names := names.qsort Name.lt
  let mut counts : NameMap Nat := {}
  let mut theoremCount : Nat := 0
  for name in names do
    let some info := env.find? name |
      throwError "GRH_AXIOM_AUDIT_FAILURE: missing declaration {name}"
    let some idx := env.getModuleIdxFor? name |
      throwError "GRH_AXIOM_AUDIT_FAILURE: missing owner for {name}"
    let some owner := modules[idx.toNat]? |
      throwError "GRH_AXIOM_AUDIT_FAILURE: invalid owner index for {name}"
    if info.isUnsafe || info.isPartial || kindOf info == "axiom" then
      throwError "GRH_AXIOM_AUDIT_FAILURE: unsafe, partial, or axiomatic declaration {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "GRH_AXIOM_AUDIT_FAILURE: {name} depends on disallowed axiom {ax}"
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
    if let .thmInfo _ := info then theoremCount := theoremCount + 1
    liftIO <| IO.println (Json.mkObj [
      ("record", toJson "grh_axiom_audit_declaration"),
      ("name", toJson name.toString),
      ("module", toJson owner.toString),
      ("kind", toJson (kindOf info)),
      ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial),
      ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString))]).compress
  for owner in owners do
    if (counts.find? owner).getD 0 == 0 then
      throwError "GRH_AXIOM_AUDIT_FAILURE: no declarations audited for {owner}"
  liftIO <| IO.println (Json.mkObj [
    ("record", toJson "grh_axiom_audit_summary"),
    ("status", toJson "PASS"),
    ("scope", toJson "native"),
    ("modules", toJson (owners.map Name.toString)),
    ("declarations", toJson names.size),
    ("theorems", toJson theoremCount),
    ("axiom_whitelist", toJson (allowed.map Name.toString))]).compress

end InfoGeometry.GRHIntegration.NativeAxiomAudit
