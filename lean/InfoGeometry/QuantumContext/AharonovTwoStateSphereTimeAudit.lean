/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AharonovTwoStateSphereTime
import InfoGeometry.External.Auto.SarsModularWeakValue

/-!
# Concrete Instantiation & Axiom Audit for Section 116: Aharonov Two-State Sphere Time
Target: `InfoGeometry/QuantumContext/AharonovTwoStateSphereTimeAudit.lean`

Verifies finite transition-amplitude identities over `ℤ`, guarded weak values over `ℚ`, and the
explicit embedding of their rational two-state subcarrier into the existing complex weak-value
owner. No physical dwell-time observable or measurement process is inferred.
-/

namespace InfoGeometry.QuantumContext.AharonovTimeAudit

open InfoGeometry.QuantumContext.AharonovTime
open InfoGeometry.QuantumContext.AharonovTime.Sphere4D
open InfoGeometry.QuantumContext.AharonovTime.SlitState2D

/-- Concrete verification over `ℤ` (`decide`) of 4D `S³` radial dilatation scaling
(`radiusSq (dilate 3 ⟨1, 2, 2, 4⟩) = 9 * 25 = 225`) and the selected unnormalized transition
amplitudes through both slits. -/
theorem sample_aharonov_sphere_time_int :
    let X : Sphere4D ℤ := ⟨1, 2, 2, 4⟩
    Sphere4D.radiusSq X = 25 ∧
    Sphere4D.radiusSq (Sphere4D.dilate 3 X) = 225 ∧
    SlitState2D.bracket SlitState2D.backwardPostSelected SlitState2D.forwardPreSelected = -1 ∧
    SlitState2D.transitionAmplitude1 SlitState2D.backwardPostSelected SlitState2D.forwardPreSelected = 1 ∧
    SlitState2D.transitionAmplitude2 SlitState2D.backwardPostSelected SlitState2D.forwardPreSelected = -2 := by
  decide

/-- Rational selected-pair weak values follow from the guarded quotient, and
    an orthogonal pair is explicitly undefined. -/
theorem sample_aharonov_guarded_weak_values_rat :
    SlitWeakValue.weakValue? SlitWeakValue.rationalBackwardPostSelected
      SlitWeakValue.rationalForwardPreSelected .slit1 = some (-1) ∧
    SlitWeakValue.weakValue? SlitWeakValue.rationalBackwardPostSelected
      SlitWeakValue.rationalForwardPreSelected .slit2 = some 2 ∧
    SlitWeakValue.weakValue? (⟨1, 0⟩ : SlitState2D ℚ) (⟨0, 1⟩ : SlitState2D ℚ)
      .slit1 = none := by
  exact ⟨SlitWeakValue.rational_selected_projector_weak_values.1,
    SlitWeakValue.rational_selected_projector_weak_values.2,
    SlitWeakValue.orthogonal_pair_weak_value_is_none⟩

/-- The selected rational weak values agree with the existing complex two-level owner. -/
theorem sample_rational_weak_values_complexified :
    SarsModularWeakValue.weakValue?
      (SlitWeakValue.complexSlitProjector .slit1)
      (SlitWeakValue.rationalStateToComplex SlitWeakValue.rationalForwardPreSelected)
      (SlitWeakValue.rationalStateToComplex SlitWeakValue.rationalBackwardPostSelected) =
        some (-1 : ℂ) ∧
    SarsModularWeakValue.weakValue?
      (SlitWeakValue.complexSlitProjector .slit2)
      (SlitWeakValue.rationalStateToComplex SlitWeakValue.rationalForwardPreSelected)
      (SlitWeakValue.rationalStateToComplex SlitWeakValue.rationalBackwardPostSelected) =
        some (2 : ℂ) := by
  constructor
  · have h := SlitWeakValue.rational_weakValue_complex_compatibility
      SlitWeakValue.rationalBackwardPostSelected
      SlitWeakValue.rationalForwardPreSelected .slit1
    rw [SlitWeakValue.rational_selected_projector_weak_values.1] at h
    simpa using h.symm
  · have h := SlitWeakValue.rational_weakValue_complex_compatibility
      SlitWeakValue.rationalBackwardPostSelected
      SlitWeakValue.rationalForwardPreSelected .slit2
    rw [SlitWeakValue.rational_selected_projector_weak_values.2] at h
    simpa using h.symm

#print axioms InfoGeometry.QuantumContext.AharonovTime.Sphere4D.unitW_ne_zero
#print axioms InfoGeometry.QuantumContext.AharonovTime.Sphere4D.radiusSq_dilate
#print axioms InfoGeometry.QuantumContext.AharonovTime.Sphere4D.shell_deviation_expansion
#print axioms InfoGeometry.QuantumContext.AharonovTime.Sphere4D.twin_shell_horizon_lock
#print axioms InfoGeometry.QuantumContext.AharonovTime.Sphere4D.twin_shell_horizon_lock_real_exp
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit1_idempotent
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit2_idempotent
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit1_projSlit2_zero
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit_partition_of_unity
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.standard_qm_slit1_nonneg
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.standard_qm_slit2_nonneg
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.two_state_transition_amplitude_partition
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.forwardPreSelected_ne_zero
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitState2D.double_slit_transition_numerators
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.weakValue?_eq_quotient_of_overlap_ne_zero
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.weakValue?_eq_none_of_overlap_eq_zero
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.slit_projector_weak_values_partition
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.orthogonal_pair_weak_value_is_none
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.weakValue?
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.rational_selected_projector_weak_values
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.complexPairing_eq_cast
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.complexProjector_action
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.complexWeakNumerator_eq_cast
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.complexWeakDenominator_eq_cast
#print axioms InfoGeometry.QuantumContext.AharonovTime.SlitWeakValue.rational_weakValue_complex_compatibility
#print axioms sample_aharonov_guarded_weak_values_rat
#print axioms sample_rational_weak_values_complexified
#print axioms sample_aharonov_sphere_time_int

end InfoGeometry.QuantumContext.AharonovTimeAudit
