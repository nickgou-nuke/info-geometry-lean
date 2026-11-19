/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Nuclear.RadonDiffusion
import Lean.Util.CollectAxioms
/-! Transitive axiom reports for every public definition and theorem in the focused owners. -/


-- RadonDiffusionProfiles
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.SolvesDiffusionDecay
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.sinhProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.coshProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.expProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.hasDerivAt_sinhProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.hasDerivAt_coshProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.hasDerivAt_expProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.deriv_sinhProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.deriv_coshProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.deriv_expProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.deriv2_sinhProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.deriv2_coshProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.deriv2_expProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.sinhProfile_solves
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.coshProfile_solves
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.expProfile_solves
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.dirichletProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.neumannProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.dirichlet_inlet
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.dirichlet_outlet
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.neumann_inlet
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.neumann_outlet_derivative
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.dirichlet_solves
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.neumann_solves
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.cellAverage
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.cellAverage_sinhProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.cellAverage_coshProfile
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.cartridgeCenter
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.cartridge_left_face
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.cartridge_right_face
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.cartridge_argument
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.sinh_at_cartridge
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.cosh_at_cartridge
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.expProfile_step
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.expProfile_halving
#print axioms InfoGeometry.Nuclear.RadonDiffusionProfiles.terminal_cosh_ratio

-- DiffusionParameters
#print axioms InfoGeometry.Nuclear.DiffusionParameters.storage_residual_factor
#print axioms InfoGeometry.Nuclear.DiffusionParameters.storage_residual_zero_iff
#print axioms InfoGeometry.Nuclear.DiffusionParameters.solves_apparent_iff_storage
#print axioms InfoGeometry.Nuclear.DiffusionParameters.sqrt_attenuation_relation
#print axioms InfoGeometry.Nuclear.DiffusionParameters.cell_attenuation_relation
#print axioms InfoGeometry.Nuclear.DiffusionParameters.diffusivity_from_cell_attenuation
#print axioms InfoGeometry.Nuclear.DiffusionParameters.linearDirichlet
#print axioms InfoGeometry.Nuclear.DiffusionParameters.constantNeumann
#print axioms InfoGeometry.Nuclear.DiffusionParameters.hasDerivAt_linearDirichlet
#print axioms InfoGeometry.Nuclear.DiffusionParameters.deriv_linearDirichlet
#print axioms InfoGeometry.Nuclear.DiffusionParameters.linearDirichlet_inlet
#print axioms InfoGeometry.Nuclear.DiffusionParameters.linearDirichlet_outlet
#print axioms InfoGeometry.Nuclear.DiffusionParameters.linearDirichlet_solves
#print axioms InfoGeometry.Nuclear.DiffusionParameters.constantNeumann_inlet
#print axioms InfoGeometry.Nuclear.DiffusionParameters.constantNeumann_outlet_derivative
#print axioms InfoGeometry.Nuclear.DiffusionParameters.constantNeumann_solves
#print axioms InfoGeometry.Nuclear.DiffusionParameters.normalizedDirichlet
#print axioms InfoGeometry.Nuclear.DiffusionParameters.normalizedDirichlet_formula

-- DiffusionTransfer
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.offDiag
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.offDiag_mul
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.offDiag_sq
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.offDiag_noncomm
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.exists_noncommuting_matrices
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.ordered_layer_mul
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.physicalGenerator
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.physicalGenerator_sq
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.physicalGenerator_sq_of_relation
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer_zero
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer_add
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer_neg_mul
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer_mul_neg
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer_det
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer_eq_generator
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer_commutator_entry
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer_noncomm
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.positive_layers_noncommute
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.exists_noncommuting_transfers

-- DiffusionTransferODE
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.hasDerivAt_transfer_entry
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.hasDerivAt_transfer_state_entry
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.transfer_state_zero
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.lossFreeTransfer
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.lossFreeTransfer_eq_generator
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.lossFreeTransfer_zero
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.lossFreeTransfer_add
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.hasDerivAt_lossFreeTransfer_entry
#print axioms InfoGeometry.Nuclear.DiffusionTransfer.lossFreeTransfer_ne_one

-- DecayAcquisitionCorrection
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.weightedExposure
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.expectedCounts
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.expectedCounts_eq_weightedExposure
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.expectedCounts_eq
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.expectedCounts_zero_rate
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.acquisitionFactor
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.acquisitionFactor_zero_rate
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.one_sub_exp_neg_pos
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.acquisitionFactor_pos
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.one_le_acquisitionFactor
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.recoverReferenceRate
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.recover_expectedCounts_pos
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.recover_expectedCounts_zero
#print axioms InfoGeometry.Nuclear.DecayAcquisitionCorrection.recover_expectedCounts

-- RadonDataAudit
#print axioms InfoGeometry.Nuclear.RadonDataAudit.counts609
#print axioms InfoGeometry.Nuclear.RadonDataAudit.counts352
#print axioms InfoGeometry.Nuclear.RadonDataAudit.liveSeconds
#print axioms InfoGeometry.Nuclear.RadonDataAudit.elapsedSeconds
#print axioms InfoGeometry.Nuclear.RadonDataAudit.startSeconds
#print axioms InfoGeometry.Nuclear.RadonDataAudit.elapsedSeconds_eq_start_sub
#print axioms InfoGeometry.Nuclear.RadonDataAudit.peakRatio
#print axioms InfoGeometry.Nuclear.RadonDataAudit.raw_ratio_three_four
#print axioms InfoGeometry.Nuclear.RadonDataAudit.raw_ratio_three_four_ne_two
#print axioms InfoGeometry.Nuclear.RadonDataAudit.peakRatio_three_gt_158
#print axioms InfoGeometry.Nuclear.RadonDataAudit.peakRatio_nine_gt_17
#print axioms InfoGeometry.Nuclear.RadonDataAudit.peakRatio_three_ne_nine
#print axioms InfoGeometry.Nuclear.RadonDataAudit.peakRatio_one_ne_three
#print axioms InfoGeometry.Nuclear.RadonDataAudit.peakRatio_first_eight_not_constant
#print axioms InfoGeometry.Nuclear.RadonDataAudit.peakRatio_not_constant
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedRate
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedRate_pos
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedRate_ne_zero
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedRate_zero_elapsed
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedRate_line_ratio
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedRate_elapsed_add
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedRate_reference_shift
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedRate_ratio_reference_shift
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedRate_roundtrip
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedPeakRatio
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedPeakRatio_eq
#print axioms InfoGeometry.Nuclear.RadonDataAudit.correctedPeakRatio_three_gt_158

-- RadonBoundaryModels
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.combinedProfile
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.hasDerivAt_combinedProfile
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.deriv_combinedProfile
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.deriv2_combinedProfile
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.combinedProfile_solves
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.combinedProfile_outlet
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.outletFlux
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.combinedProfile_outletFlux
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robin_coefficient_iff
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robin_ambient_coefficient_iff
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.dirichlet_zero_value_positive_flux
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.dirichlet_outletFlux
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.linearDirichlet_outletFlux
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.dirichlet_linear_outletFlux_ratio
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.twoReservoir
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.twoReservoir_inlet
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.twoReservoir_outlet
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.twoReservoir_solves
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.twoReservoir_formula
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robinDenominator
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robinProfile
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robinProfile_formula
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robinDenominator_pos
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robinProfile_inlet
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robinProfile_solves
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robinProfile_boundary
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robinProfile_zero
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.robinProfile_one
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.shiftedSinh
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.shiftedSinh_expansion
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.shiftedSinh_robin_iff
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.shiftedSinh_tanh_relation
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.shiftedSinh_robin_gt
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.sinh_add_exponential_decomposition
#print axioms InfoGeometry.Nuclear.RadonBoundaryModels.exp_lt_sinh_step_ratio

-- RadonObservationArtifacts
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.withConstantOffset
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.deriv_withConstantOffset
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.constantOffset_residual
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.constantOffset_solves_iff
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.constantOffset_not_solves
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.constantOffset_source_balance
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.affineObservation
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.affineObservation_shift
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.mixtureRatio
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.mixtureRatio_eq_response_ratio_iff
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.pointCorrection_background
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.countsWithBackground
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.recover_background_subtracted
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.lossyObservation
#print axioms InfoGeometry.Nuclear.RadonObservationArtifacts.lossyObservation_affine_clock

-- DetectorBeerLambert
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.collisionDensity
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.collisionIntegral
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.acceptedRayIntegral
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.continuous_collisionDensity
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.hasDerivAt_collisionPrimitive
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.collisionIntegral_eq
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.collisionDensity_nonneg
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.collisionIntegral_nonneg
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.collisionIntegral_le_one
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.collisionIntegral_mem_unitInterval
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.collisionIntegral_zero
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.integrable_acceptedRay
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.acceptedRay_nonneg
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.acceptedRay_le_collision
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.acceptedRay_le_one
#print axioms InfoGeometry.Nuclear.DetectorBeerLambert.partialCollisionIntegral_eq

/- Also inspect private and generated declarations, and fail the check if any
transitive dependency uses an axiom beyond Mathlib's standard foundations. -/
open Lean in
run_cmd do
  let prefixes : Array Name := #[
    `InfoGeometry.Nuclear.RadonDiffusionProfiles,
    `InfoGeometry.Nuclear.DiffusionParameters,
    `InfoGeometry.Nuclear.DiffusionTransfer,
    `InfoGeometry.Nuclear.DecayAcquisitionCorrection,
    `InfoGeometry.Nuclear.RadonDataAudit,
    `InfoGeometry.Nuclear.RadonBoundaryModels,
    `InfoGeometry.Nuclear.RadonObservationArtifacts,
    `InfoGeometry.Nuclear.DetectorBeerLambert]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut union : Array Name := #[]
  for (name, _) in (← getEnv).constants do
    let userName := (privateToUserName? name).getD name
    if prefixes.any (fun ns => ns.isPrefixOf userName) then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
        unless union.contains axiomName do
          union := union.push axiomName
      logInfo m!"AXIOMS {name}: {axioms.toList}"
      count := count + 1
  if count == 0 then throwError "No task declarations found"
  logInfo m!"AUDIT_TOTAL {count} declarations; AXIOM_UNION {union.toList}"
