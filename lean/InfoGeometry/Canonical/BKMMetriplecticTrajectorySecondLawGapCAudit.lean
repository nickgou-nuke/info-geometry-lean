/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Gap C Axiom and Integrity Audit for `BKMMetriplecticTrajectorySecondLaw`

Non-clobbering Gap C audit module reproducing all 66 `#print axioms` checks from
`89df80d1f6:lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawAudit.lean`
and running an environment-wide `Lean.Util.CollectAxioms` sweep verifying strictly
`{propext, Classical.choice, Quot.sound}` across all exported declarations.

Note: `lean/InfoGeometry/Canonical/BKMMetriplecticTrajectorySecondLawAudit.lean` on
`HEAD` belongs to `InfoGeometry.Canonical.RegularSupportSecondLaw` (external commit
`41d8b01527`) and is left untouched.
-/

#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.banach_metriplectic_hasDerivAt_eq
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.banach_metriplectic_hasDerivAt_nonpos
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.banach_metriplectic_deriv_nonpos
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.banach_metriplectic_antitoneOn
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.banach_metriplectic_antitone
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.genericMetriplectic_freeEnergy_hasDerivAt_nonpos
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.genericMetriplectic_freeEnergy_antitoneOn
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.genericMetriplectic_entropy_monotoneOn
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.genericMetriplectic_freeEnergy_antitoneOn_finiteDim

#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.gibbsRelativePotential
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.gibbsRelativePotentialFDeriv
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.gibbsRelativePotentialFDeriv_apply
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.gibbsRelativePotentialFDeriv_apply_of_isSelfAdjoint
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasFDerivAt_gibbsRelativePotential
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasFDerivAt_gibbsRelativePotential_of_isSelfAdjoint
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.gibbsUnitaryVectorField
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.gibbsBKMDissipativeField
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.gibbsMetriplecticFlow
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.isSelfAdjoint_gibbsUnitaryVectorField
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.isSelfAdjoint_gibbsBKMDissipativeField
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.isSelfAdjoint_gibbsMetriplecticFlow
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.finiteOperatorTrace_mul_commutator_eq_zero_of_commute
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.commute_normalizedExponential_self
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.finiteOperatorTrace_sub_mul_gibbsUnitaryVectorField_eq_zero
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.finiteOperatorTrace_gibbsUnitaryVectorField_re_eq_zero
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasDerivAt_gibbsRelativePotential_metriplectic
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.deriv_gibbsRelativePotential_metriplectic_nonpos
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.deriv_gibbsRelativePotential_metriplectic_neg_of_ne
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.antitoneOn_gibbsRelativePotential_metriplectic
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.integral_exp_smul_commutator_eq
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.kuboMoriTransform_commutator_eq_commutator_rho
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.kuboMoriTransform_commutator_eq_commutator_normalizedExponential
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.normalizedExponentialFDeriv
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasFDerivAt_normalizedExponential
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.inv_tracedExponential_smul_duhamelDerivative_eq_kuboMoriTransform
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.kuboMoriTransform_one
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.normalizedExponentialFDeriv_apply_eq_kuboMoriTransform
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.normalizedExponentialFDeriv_apply_eq_kuboMoriTransform_centered
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasDerivAt_normalizedExponential
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasDerivAt_normalizedExponential_centered
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasDerivAt_normalizedExponential_gibbsMetriplecticFlow
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasDerivAt_normalizedExponential_naturalGradientMetriplectic

#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.matrixOfOpLinearℝ
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.matrixOfOpLinearℝ_apply
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.matrixOpLinearℝ
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.matrixOpLinearℝ_apply
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.matrixOfOpEquivℝ
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.finiteDimensional_real_finiteOperatorAlgebra
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.matrixOfOpCLMℝ
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.matrixOfOpCLMℝ_apply
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.matrixOpCLMℝ
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.matrixOpCLMℝ_apply
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasDerivAt_freeEnergy_of_matrixKuboMoriMobility
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.antitoneOn_freeEnergy_of_matrixKuboMoriMobility
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility_of_commuting_state
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.antitoneOn_freeEnergy_of_matrixKuboMoriMobility_of_commuting_state
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.deriv_freeEnergy_nonpos_of_matrixKuboMoriMobility_of_reversible_orthogonal
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.antitoneOn_freeEnergy_of_matrixKuboMoriMobility_of_reversible_orthogonal
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.evolvingGibbsMetriplecticSystem
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasDerivAt_matrixNormalizedExponential_metriplectic
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.traceNormalizedSquarePotential
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.traceNormalizedSquarePotentialFDeriv
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasFDerivAt_traceNormalizedSquarePotential
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.hasDerivAt_traceNormalizedSquarePotential_gibbsTrajectory
#print axioms InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw.antitoneOn_traceNormalizedSquarePotential_gibbsTrajectory

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owner : Name := `InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless moduleNames.contains owner do
    throwError "AUDIT_FAILURE: missing imported owner {owner}"
  let mut count : Nat := 0
  let mut theorems : Nat := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let some modName := moduleNames[moduleIdx.toNat]? | continue
    if modName != owner then continue
    if let .axiomInfo _ := info then
      throwError "AUDIT_FAILURE: introduced axiom {name}"
    if info.isUnsafe || info.isPartial then
      throwError "AUDIT_FAILURE: unsafe or partial declaration {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "AUDIT_FAILURE: {name} depends on disallowed axiom {ax}"
      if !used.contains ax then used := used.push ax
    count := count + 1
    if let .thmInfo _ := info then theorems := theorems + 1
  if count == 0 then
    throwError "AUDIT_FAILURE: empty audited owner {owner}"
  logInfo m!"AUDIT_OWNER: {owner}: {count} declarations ({theorems} theorems)"
  logInfo m!"AUDIT_AXIOMS: {used.qsort Name.lt}"
  logInfo m!"AUDIT_SUCCESS: {owner} verified clean"
