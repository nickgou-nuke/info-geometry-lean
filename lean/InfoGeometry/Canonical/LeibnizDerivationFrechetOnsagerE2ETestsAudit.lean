/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerE2ETests
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom and Integrity Audit for `LeibnizDerivationFrechetOnsagerE2ETests`

Verifies via both explicit `#print axioms` on every exported E2E witness definition and
Tier 1–5 theorem, plus an environment-wide `Lean.Util.CollectAxioms` sweep, that all constants in
`InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerE2ETests` depend strictly on
`{propext, Classical.choice, Quot.sound}`.
-/

section ExplicitPrintAxioms

open InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerE2ETests

-- Shared Concrete Noncommutative Witness Kit
#print axioms A_swap
#print axioms B_tilt
#print axioms P_d63
#print axioms P_diag_mat
#print axioms P_diag
#print axioms H_d63
#print axioms Q_odd
#print axioms K1_real
#print axioms K2_real
#print axioms hK12_real_noncomm
#print axioms hA_swap_sa
#print axioms hB_tilt_sa
#print axioms hH_d63_sa
#print axioms hZ_d63_pos
#print axioms hQ_odd_anti
#print axioms hMat2C_noncomm_witness
#print axioms hMat2Ext_noncomm_witness
#print axioms hMat3C_noncomm_witness
#print axioms hAB_noncomm
#print axioms hHA_noncomm
#print axioms hP_diag_P_d63_noncomm
#print axioms P_real2_mat
#print axioms P_real2
#print axioms P_real2_apply
#print axioms P_real2_idem
#print axioms P_real2_selfAdjoint
#print axioms CIK_real2
#print axioms B_real2
#print axioms tilt_real2
#print axioms B_ns
#print axioms B_sing
#print axioms B_sat
#print axioms triad_pos
#print axioms triad_sat
#print axioms triad_zero
#print axioms M_tkk
#print axioms M_tkk_psd
#print axioms M_tkk_dual
#print axioms conformalBlock_nc

-- Tier 1 & Tier 2: Gap A (F1, F2, F3)
#print axioms t1_f1_01_cartanTimeReversal
#print axioms t1_f1_02_cartanInvolutionTimeReversal
#print axioms t1_f1_03_cartanParityOnsagerSystem
#print axioms t1_f1_04_drazinCartanParityOnsagerSystem
#print axioms t1_f1_05_cartanMasterReciprocityAndEntropy
#print axioms t1_f2_01_scalarSchurEffective
#print axioms t1_f2_02_drazinPenroseTriad
#print axioms t1_f2_03_tkkParityOnsagerSystem
#print axioms t1_f2_04_conformalOnsagerBlock
#print axioms t1_f2_05_conformalPKMetriplecticSplit
#print axioms t1_f3_01_peirceSymmetricLieAlgebra
#print axioms t1_f3_02_peirceAdKerRange
#print axioms t1_f3_03_peirceCartanSplitAndEquiv
#print axioms t1_f3_04_peirceCutDerivationLieLane
#print axioms t1_f3_05_cutDerivationPowersAlign
#print axioms t2_f1_01_signFlipParity
#print axioms t2_f1_02_degenerateIdInvolution
#print axioms t2_f1_03_reversibleOnlyZeroOnsager
#print axioms t2_f1_04_nonabelianCartanBrackets
#print axioms t2_f1_05_negativeDissipativeCounterexample
#print axioms t2_f2_01_singularHiddenBlock
#print axioms t2_f2_02_schurComplementSaturation
#print axioms t2_f2_03_bodyForcePositivityVsZero
#print axioms t2_f2_04_tkkDualDualAndZeroMatrix
#print axioms t2_f2_05_conformalCommutatorVsCommutingLimit
#print axioms t2_f3_01_zeroProjector
#print axioms t2_f3_02_identityProjector
#print axioms t2_f3_03_noncommutingPeirceCuts
#print axioms t2_f3_04_nonIdempotentBoundary
#print axioms t2_f3_05_dim0VsDim2Boundary

-- Tier 1 & Tier 2: Gap B (F4, F5)
#print axioms t1_f4_01_bkmStarInvariance
#print axioms t1_f4_02_starDerivationParitySystem
#print axioms t1_f4_03_autDerivationParitySystem
#print axioms t1_f4_04_finiteGibbsCEParitySystem
#print axioms t1_f4_05_finiteGibbsFamilyNOperatorParity
#print axioms t1_f4_06_erlangenDatumSpecialization
#print axioms t1_f5_01_frechetFormToCEFormDegrees0123
#print axioms t1_f5_02_frechetExtDerivEqCeExterior
#print axioms t1_f5_03_ceCurvatureEqAndBkmProbe
#print axioms t1_f5_04_logPartitionHessianAlignment
#print axioms t1_f5_05_parityOnsagerFormPairingDegrees12
#print axioms t2_f4_01_zeroProbeSystem
#print axioms t2_f4_02_starSignFlipProbe
#print axioms t2_f4_03_autSignFlipAndBadHamiltonian
#print axioms t2_f4_04_emptyFamilyAndZeroWeights
#print axioms t2_f4_05_identityVsNoncommFamily
#print axioms t2_f5_01_exteriorDerivNilpotency
#print axioms t2_f5_02_complexVsRealScalarAndZeroIm
#print axioms t2_f5_03_ceCurvatureAlternatingVsNoncomm
#print axioms t2_f5_04_closedAndConstantForms
#print axioms t2_f5_05_degree0AndDim0Boundary

-- Tier 1 & Tier 2: Gap C (F6)
#print axioms t1_f6_01_banachMetriplecticFlow
#print axioms t1_f6_02_gibbsRelativePotentialMetriplectic
#print axioms t1_f6_03_kuboMoriTransformCommutator
#print axioms t1_f6_04_hasDerivAtNormalizedExponential
#print axioms t1_f6_05_freeEnergyMatrixKuboMoriMobility
#print axioms t2_f6_01_strictNegVsEquilibriumZero
#print axioms t2_f6_02_slitPlaneBoundary
#print axioms t2_f6_03_noncommutingTrajectory
#print axioms t2_f6_04_noncommutingReversibleCancellationFailure
#print axioms t2_f6_05_dim0SlitPlaneBoundary
#print axioms t2_f6_06_degenerateKernelBoundary

-- Tier 1 & Tier 2: Gap D (F7, F8)
#print axioms t1_f7_01_modularZDerivationsRoundTrip
#print axioms t1_f7_02_modularRLinearDerivations
#print axioms t1_f7_03_colimitTowerAndLocalSystem
#print axioms t1_f7_04_outerAndStandaloneWrappers
#print axioms t1_f7_05_properSubtypesAndOnsagerFormPairing
#print axioms t2_f7_01_scalarDerivationNoncommBoundary
#print axioms t2_f7_02_outerDerivationProperSubtypeBoundary
#print axioms t2_f7_03_starDerivationProperSubtypeBoundary
#print axioms t2_f7_04_modularNonAbelianBracket
#print axioms t2_f7_05_scalarCarrierHypothesisBoundary
#print axioms t1_f8_01_threeG2Derivations
#print axioms t1_f8_02_splitCayleyAndSplitOctonionDerivations
#print axioms t1_f8_03_zornJordanAndH3ZornDerivations
#print axioms t1_f8_04_squareZeroAndPeirceSuperanticommutator
#print axioms t1_f8_05_braidedDegreeZeroEmbedding
#print axioms t2_f8_01_diamondAndInstanceLeakGuard
#print axioms t2_f8_02_squareZeroPeirceNoGo
#print axioms t2_f8_03_oddSuperderivationVsOrdinaryLeibniz
#print axioms t2_f8_04_braidedDegree1VsDegree0Boundary
#print axioms t2_f8_05_nonAssociativityWithLeibniz

-- Tier 3: Cross-Feature Pairwise Combinations (T3-AB..T3-AC)
#print axioms t3_ab_01_peirceCutCeBkmParity
#print axioms t3_ab_02_cartanSplitParityFormPairing
#print axioms t3_bc_01_02_frechetHessianAndGibbsTrajectorySecondLaw
#print axioms t3_ad_01_peirceCutSuperAnticommCartan
#print axioms t3_ad_02_bridgedLaneCartanOnsager
#print axioms t3_db_01_modularDerivationCeBkmParityForm
#print axioms t3_db_02_superBraidedCeBkmCurvature
#print axioms t3_cd_01_modularDerivationMetriplecticFlow
#print axioms t3_cd_02_exceptionalSuperDerivationMetriplecticFlow
#print axioms t3_ac_01_cartanSchurMetriplecticFlow
#print axioms t3_ac_02_peirceCutMatrixKuboMori

-- Tier 4: Real-World End-to-End Scenarios (T4-SC-01..T4-SC-05)
#print axioms t4_sc_01_quantumGibbsBkmRelaxationPipeline
#print axioms t4_sc_02_blackHolePeirceCartanMetriplectic
#print axioms t4_sc_03_singularSchurDrazinBodyForcePipeline
#print axioms t4_sc_04_kmsModularExteriorCurvaturePipeline
#print axioms t4_sc_05_exceptionalJordanSuperBraidedPipeline

-- Additional Exported Witness & Helper Declarations (Tiers 1-4)
#print axioms matrixOfOp_sub_eq
#print axioms matrixOfOp_neg_eq
#print axioms matrixOfOp_mul_eq
#print axioms matrixOfOp_one_eq
#print axioms P_doubled_proj
#print axioms P_doubled_proj_idem
#print axioms P_doubled_proj_selfAdjoint
#print axioms CIK_doubled
#print axioms B_doubled
#print axioms isSelfAdjoint_I_smul_comm
#print axioms isSelfAdjoint_real_smul
#print axioms isSelfAdjoint_add_op
#print axioms switchOp2_eq_A_swap
#print axioms matrixOfOp_tiltOp2
#print axioms matrixOfOp_A_swap
#print axioms matrixOfOp_B_tilt
#print axioms matrixOfOp_H_d63
#print axioms traceMulAlt2CLM
#print axioms Φ_norm_swap
#print axioms omega0Smooth
#print axioms omega3Const
#print axioms H_sol_c
#print axioms H_sol_d
#print axioms H_sol_curve
#print axioms H_sol_curve_isSelfAdjoint
#print axioms Mat2R
#print axioms Mat2C
#print axioms innerMat2RDeriv
#print axioms innerMat2CDeriv
#print axioms ncZornRot01Fun
#print axioms P3_mat_e2e
#print axioms P3_op_e2e
#print axioms P3_op_e2e_idem
#print axioms P3_e2e
#print axioms A3_e2e
#print axioms C3_e2e
#print axioms X3_e2e
#print axioms Y3_e2e
#print axioms P_diag_i_mat
#print axioms P_diag_i
#print axioms conjStarAlgEquiv_realMatrix
#print axioms conjStarAlgEquiv_B_tilt
#print axioms conjStarAlgEquiv_A_swap
#print axioms H3_e2e
#print axioms B_br_e2e
#print axioms H3_e2e_sa
#print axioms X3_e2e_sa
#print axioms D_br_e2e
#print axioms D_br_e2e_isLeibniz

-- Tier 5 Helpers & Adversarial Coverage Hardening (T5-CAP-01, T5-A..T5-D)
#print axioms star_I_comm_e2e
#print axioms comm_leib_op_e2e
#print axioms peirce_conj_odd_deriv_e2e
#print axioms peirce_conj_odd_deriv_rev_e2e
#print axioms op_invS_eq_e2e
#print axioms peirce_P_minus_apply_e2e
#print axioms p_d63_mat_eq_e2e
#print axioms switchOp2_mat_eq_e2e
#print axioms tiltOp2_twist_neg_e2e
#print axioms opZornComm_e2e
#print axioms odd_twist_leibniz_e2e
#print axioms odd_twist_anticomm_e2e
#print axioms opZornCommDeriv_e2e
#print axioms d_odd_lin_e2e
#print axioms U_rot_e2e
#print axioms H_ng_sa_e2e
#print axioms t5_cap_01_capstone_umbrella
#print axioms t5_a_01_cartan_pos_parity_and_drazin
#print axioms t5_a_02_two_block_schur_tkk_conformal_flip
#print axioms t5_a_03_peirce_cut_bkm_and_cut_stabilizer
#print axioms t5_d_01_modular_nondegenerate_and_lie_lanes
#print axioms t5_d_02_nonconstant_colimit_tower_and_injectivity
#print axioms t5_d_03_opzorn_and_nontrivial_graded_braided
#print axioms t5_b_01_oddParity_erlangenAut_frechetFormPairing
#print axioms t5_b_02_modularInterpolation_and_jetVsForm
#print axioms t5_c_01_genericMetriplectic_coupled
#print axioms t5_c_02_nonTracial_nonCommuting_trajectories
#print axioms t5_c_02b_matrixNormalized_evolvingGibbs
#print axioms t5_c_03_slitPlane_and_nonSA

end ExplicitPrintAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owner : Name := `InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerE2ETests
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
