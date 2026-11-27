/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometryGRH.VerifiedGRH
import InfoGeometryGRH.PrimeRemainderBridge
import InfoGeometryGRH.RealDoubledGRH
import InfoGeometry.Arithmetic.SmoothedMangoldtMellin
import InfoGeometry.Krein.Clifford
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Data.Json

/-!
# Trust audit of the concrete GRH integration

The printed endpoint reports are human-readable evidence. The command below
also rejects nonstandard transitive axioms and unsafe, partial, or axiomatic
declarations in every selected owner, including private/generated constants.
Thus merely printing an axiom report is not the acceptance gate.

This audit checks the proof trust boundary, not whether a theorem's hypotheses
match a proposed mathematical interpretation. Source review remains separate.
-/

#print axioms New.grh
#print axioms InfoGeometry.GRHIntegration.dirichletRightHalfPlaneNonvanishing
#print axioms InfoGeometry.GRHIntegration.riemannHypothesis
#print axioms InfoGeometry.GRHIntegration.dirichletL_zeros_on_line
#print axioms InfoGeometry.GRHIntegration.centeredSmoothing_div_eq_primeRemainder
#print axioms InfoGeometry.GRHIntegration.weightedMangoldt_integerCenteredSqrtBound
#print axioms InfoGeometry.GRHIntegration.integrableOn_centeredSmoothing_mellin
#print axioms InfoGeometry.GRHIntegration.integral_centeredSmoothing_mellin
#print axioms InfoGeometry.GRHIntegration.isPolar_centeredSmoothing_div_exp
#print axioms InfoGeometry.Arithmetic.RealDoubledDirichletReadout.scalarOp_eq_zero_iff
#print axioms InfoGeometry.GRHIntegration.realDirichletReadout_zero_re
#print axioms InfoGeometry.GRHIntegration.realCenteredXiReadout_zero_offset
#print axioms InfoGeometry.Krein.rot45Conj_symm_apply_apply

open Lean Elab Command

namespace InfoGeometry.GRHIntegration.AxiomAudit

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
  `InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout,
  `InfoGeometryGRH.VerifiedGRH,
  `InfoGeometryGRH.PrimeRemainderBridge,
  `InfoGeometryGRH.RealDoubledGRH]

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
    ("scope", toJson "integration"),
    ("modules", toJson (owners.map Name.toString)),
    ("declarations", toJson names.size),
    ("theorems", toJson theoremCount),
    ("axiom_whitelist", toJson (allowed.map Name.toString))]).compress

end InfoGeometry.GRHIntegration.AxiomAudit
