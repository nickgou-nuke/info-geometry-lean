/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.PhaseObservableUncertainty
import InfoGeometry.Canonical.HestenesModularBregman
import InfoGeometry.Geometry.RealHamiltonianMoment

open scoped InnerProductSpace

/-!
# Centered bounded-observable uncertainty on the real doubled carrier

The expectation is the existing positive Hilbert readout. Observable centering,
variance, and covariance use bounded real operators on `DoubledSpace E`.
The phase operator is explicit: its square is `-Id`, its Hilbert adjoint is
its negative, and each observable commutes with it. No complex scalar field
is introduced.

Normalization is required for the zero-mean and second-moment identities.
The norm area inequality and its commutator readout hold for every state.
The canonical phase `K = Jε` and a Hestenes right phase action can therefore
specialize the same theorem without being identified with one another.
The phase Gram and arbitrary-shift commutator theorems are reused from
`Krein.InternalPhaseGram`, `Krein.PhaseLinearObservableCommutator`, and
`Canonical.PhaseObservableUncertainty`.
-/

namespace InfoGeometry.Canonical.OperatorialUncertainty

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.HestenesModularBregman

section CenteredObservables

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Subtract the existing Hilbert expectation times the identity operator. -/
@[rep_depth operator]
noncomputable def centeredObservable (psi : H₂) (A : EndH) : EndH :=
  A - hilbertExpectationAt (E := E) psi A • ContinuousLinearMap.id ℝ H₂

/-- The squared norm of the centered observable applied to the state. -/
@[rep_depth operator]
noncomputable def hilbertVarianceAt (psi : H₂) (A : EndH) : ℝ :=
  ‖centeredObservable (E := E) psi A psi‖ ^ 2

/-- The real Hilbert pairing of the two centered observable vectors. -/
@[rep_depth operator]
noncomputable def hilbertCovarianceAt (psi : H₂) (A B : EndH) : ℝ :=
  ⟪centeredObservable (E := E) psi A psi,
    centeredObservable (E := E) psi B psi⟫_ℝ

/-- The actual commutator, read against the phase-rotated state. -/
@[rep_depth operator]
noncomputable def phaseCommutatorAt (P : EndH) (psi : H₂) (A B : EndH) : ℝ :=
  ⟪P psi, transportCommutator (E := E) A B psi⟫_ℝ

@[rep_depth operator, simp]
theorem centeredObservable_apply (psi : H₂) (A : EndH) (u : H₂) :
    centeredObservable (E := E) psi A u
      = A u - hilbertExpectationAt (E := E) psi A • u := by
  rfl

/-- Centering has zero expectation at a unit state. -/
@[rep_depth operator]
theorem hilbertExpectationAt_centeredObservable_eq_zero
    (psi : H₂) (A : EndH) (hpsi : ‖psi‖ = 1) :
    hilbertExpectationAt (E := E) psi (centeredObservable (E := E) psi A) = 0 := by
  simp [hilbertExpectationAt, centeredObservable, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hpsi]

/-- The centered observable remains Hilbert self-adjoint. -/
@[rep_depth operator]
theorem centeredObservable_isSelfAdjoint
    (psi : H₂) (A : EndH) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (centeredObservable (E := E) psi A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  change
    ⟪A u - hilbertExpectationAt (E := E) psi A • u, v⟫_ℝ
      = ⟪u, A v - hilbertExpectationAt (E := E) psi A • v⟫_ℝ
  rw [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hA.isSymmetric u v]

/-- A real identity shift preserves commutation with any phase operator. -/
@[rep_depth operator]
theorem centeredObservable_comp_phase_eq
    (P : EndH) (psi : H₂) (A : EndH)
    (hAP : A.comp P = P.comp A) :
    (centeredObservable (E := E) psi A).comp P
      = P.comp (centeredObservable (E := E) psi A) := by
  apply ContinuousLinearMap.ext
  intro u
  have hEval : A (P u) = P (A u) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : EndH => T u) hAP
  change
    A (P u) - hilbertExpectationAt (E := E) psi A • P u
      = P (A u - hilbertExpectationAt (E := E) psi A • u)
  rw [map_sub, map_smul, hEval]

/-- Centering preserves the existing canonical `K = Jε` phase-linearity predicate. -/
@[rep_depth operator]
theorem centeredObservable_isPhaseLinear
    (psi : H₂) (A : EndH) (hA : IsPhaseLinear (E := E) A) :
    IsPhaseLinear (E := E) (centeredObservable (E := E) psi A) := by
  exact centeredObservable_comp_phase_eq (E := E)
    (InfoGeometry.Krein.clockAxis (E := E)) psi A hA

/-- Real identity shifts do not change the full noncommutative commutator. -/
@[rep_depth operator]
theorem transportCommutator_sub_smul_id
    (A B : EndH) (a b : ℝ) :
    transportCommutator (E := E)
        (A - a • ContinuousLinearMap.id ℝ H₂)
        (B - b • ContinuousLinearMap.id ℝ H₂)
      = transportCommutator (E := E) A B := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [transportCommutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_sub, map_smul, smul_sub, smul_smul]
  rw [mul_comm a b]
  abel

/-- Observable centering leaves the commutator operator unchanged. -/
@[rep_depth operator]
theorem transportCommutator_centeredObservable
    (psi : H₂) (A B : EndH) :
    transportCommutator (E := E)
        (centeredObservable (E := E) psi A)
        (centeredObservable (E := E) psi B)
      = transportCommutator (E := E) A B := by
  exact transportCommutator_sub_smul_id (E := E) A B
    (hilbertExpectationAt (E := E) psi A)
    (hilbertExpectationAt (E := E) psi B)

/-- Variance is nonnegative without requiring self-adjointness. -/
@[rep_depth operator]
theorem hilbertVarianceAt_nonneg (psi : H₂) (A : EndH) :
    0 ≤ hilbertVarianceAt (E := E) psi A :=
  sq_nonneg _

/-- At a unit state, the centered squared norm is the norm second moment minus the mean square. -/
@[rep_depth operator]
theorem hilbertVarianceAt_eq_norm_sq_sub_sq
    (psi : H₂) (A : EndH) (hpsi : ‖psi‖ = 1) :
    hilbertVarianceAt (E := E) psi A
      = ‖A psi‖ ^ 2 - (hilbertExpectationAt (E := E) psi A) ^ 2 := by
  rw [hilbertVarianceAt, centeredObservable_apply, norm_sub_sq_real,
    real_inner_smul_right, real_inner_comm (A psi) psi,
    norm_smul, hpsi, mul_one, Real.norm_eq_abs, sq_abs]
  unfold hilbertExpectationAt
  ring

/-- The second operator moment of a Hilbert self-adjoint observable is its squared output norm. -/
@[rep_depth operator]
theorem hilbertExpectationAt_comp_self_eq_norm_sq
    (psi : H₂) (A : EndH) (hA : IsSelfAdjoint A) :
    hilbertExpectationAt (E := E) psi (A.comp A) = ‖A psi‖ ^ 2 := by
  calc
    hilbertExpectationAt (E := E) psi (A.comp A)
        = ⟪psi, A (A psi)⟫_ℝ := rfl
    _ = ⟪A psi, A psi⟫_ℝ := (hA.isSymmetric psi (A psi)).symm
    _ = ‖A psi‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- The usual second-moment variance formula, with its unit-state hypothesis explicit. -/
@[rep_depth operator]
theorem hilbertVarianceAt_eq_expectation_comp_self_sub_sq
    (psi : H₂) (A : EndH) (hA : IsSelfAdjoint A) (hpsi : ‖psi‖ = 1) :
    hilbertVarianceAt (E := E) psi A
      = hilbertExpectationAt (E := E) psi (A.comp A)
        - (hilbertExpectationAt (E := E) psi A) ^ 2 := by
  have hUnit : ⟪psi, psi⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hpsi, one_pow]
  simpa only [hilbertVarianceAt, centeredObservable_apply, hilbertExpectationAt,
    PhaseLinearObservableCommutator.centeredVector] using
    PhaseObservableUncertainty.centered_norm_sq_eq_second_moment_sub_mean_sq
      A hA psi hUnit

/-- Centered covariance expands to the raw pairing minus the product of the means. -/
@[rep_depth operator]
theorem hilbertCovarianceAt_eq_inner_sub_mul
    (psi : H₂) (A B : EndH) (hpsi : ‖psi‖ = 1) :
    hilbertCovarianceAt (E := E) psi A B
      = ⟪A psi, B psi⟫_ℝ
        - hilbertExpectationAt (E := E) psi A * hilbertExpectationAt (E := E) psi B := by
  have hUnit : ⟪psi, psi⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hpsi, one_pow]
  unfold hilbertCovarianceAt
  simp only [centeredObservable_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hUnit,
    real_inner_comm (A psi) psi]
  unfold hilbertExpectationAt
  ring

/-- The untwisted real expectation of a commutator of self-adjoint operators vanishes. -/
@[rep_depth operator]
theorem hilbertExpectationAt_transportCommutator_eq_zero
    (psi : H₂) (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    hilbertExpectationAt (E := E) psi (transportCommutator (E := E) A B) = 0 := by
  unfold hilbertExpectationAt transportCommutator
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, inner_sub_right]
  rw [← hA.isSymmetric psi (B psi), ← hB.isSymmetric psi (A psi),
    real_inner_comm (A psi) (B psi), sub_self]

/-- The anticommutator gives twice the Hilbert pairing of the two observable vectors. -/
@[rep_depth operator]
theorem hilbertExpectationAt_anticommutator_eq_two_inner
    (psi : H₂) (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    hilbertExpectationAt (E := E) psi (A.comp B + B.comp A)
      = 2 * ⟪A psi, B psi⟫_ℝ := by
  unfold hilbertExpectationAt
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_right]
  rw [← hA.isSymmetric psi (B psi), ← hB.isSymmetric psi (A psi),
    real_inner_comm (B psi) (A psi)]
  ring

/-- Centered covariance is the half-anticommutator readout. -/
@[rep_depth operator]
theorem hilbertExpectationAt_centered_anticommutator_eq_two_covariance
    (psi : H₂) (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    hilbertExpectationAt (E := E) psi
        ((centeredObservable (E := E) psi A).comp (centeredObservable (E := E) psi B)
          + (centeredObservable (E := E) psi B).comp (centeredObservable (E := E) psi A))
      = 2 * hilbertCovarianceAt (E := E) psi A B := by
  exact hilbertExpectationAt_anticommutator_eq_two_inner (E := E) psi
    (centeredObservable (E := E) psi A) (centeredObservable (E := E) psi B)
    (centeredObservable_isSelfAdjoint (E := E) psi A hA)
    (centeredObservable_isSelfAdjoint (E := E) psi B hB)

/--
The sign and factor of the actual phase-twisted commutator follow from
self-adjointness, phase commutation, and the skew adjoint of the phase.
-/
@[rep_depth operator]
theorem phaseCommutatorAt_eq_two_inner
    (P : EndH) (psi : H₂) (A B : EndH)
    (hPstar : star P = -P) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : A.comp P = P.comp A) (hBP : B.comp P = P.comp B) :
    phaseCommutatorAt (E := E) P psi A B = 2 * ⟪P (A psi), B psi⟫_ℝ := by
  exact
    (PhaseLinearObservableCommutator.twice_phase_pair_eq_commutator_of_phase
      P (PhaseLinearObservableCommutator.phase_pair_neg_swap_of_star_eq_neg P hPstar)
      A B hA hB hAP hBP psi).symm

/-- The actual commutator readout equals twice the phase area of the centered vectors. -/
@[rep_depth operator]
theorem phaseCommutatorAt_eq_two_inner_centered
    (P : EndH) (psi : H₂) (A B : EndH)
    (hPstar : star P = -P) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : A.comp P = P.comp A) (hBP : B.comp P = P.comp B) :
    phaseCommutatorAt (E := E) P psi A B
      = 2 * ⟪P (centeredObservable (E := E) psi A psi),
          centeredObservable (E := E) psi B psi⟫_ℝ := by
  simpa only [phaseCommutatorAt, transportCommutator, centeredObservable_apply,
    PhaseLinearObservableCommutator.centeredVector] using
    (PhaseLinearObservableCommutator.twice_centered_phase_pair_eq_commutator_of_phase
      P (PhaseLinearObservableCommutator.phase_pair_neg_swap_of_star_eq_neg P hPstar)
      A B hA hB hAP hBP
      (hilbertExpectationAt (E := E) psi A) (hilbertExpectationAt (E := E) psi B) psi).symm

/--
Real Robertson--Schrödinger uncertainty with the actual operator commutator.
All products remain compositions of bounded operators on the doubled carrier.
-/
@[rep_depth operator]
theorem hilbertCovariance_sq_add_phaseCommutator_sq_div_four_le
    (P : EndH) (psi : H₂) (A B : EndH)
    (hP : IsRealComplexStructure P.toLinearMap) (hPstar : star P = -P)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : A.comp P = P.comp A) (hBP : B.comp P = P.comp B) :
    (hilbertCovarianceAt (E := E) psi A B) ^ 2
        + (phaseCommutatorAt (E := E) P psi A B) ^ 2 / 4
      ≤ hilbertVarianceAt (E := E) psi A * hilbertVarianceAt (E := E) psi B := by
  have hPnorm (u : H₂) : ‖P u‖ = ‖u‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact InfoGeometry.Geometry.RealHamiltonianMoment.inner_map_map P hP hPstar u u
  simpa only [hilbertCovarianceAt, hilbertVarianceAt, centeredObservable_apply,
    phaseCommutatorAt, transportCommutator, PhaseLinearObservableCommutator.centeredVector,
    div_eq_mul_inv, one_mul, mul_comm] using
    PhaseObservableUncertainty.centered_robertson_schrodinger_of_phase
      P hPnorm (PhaseLinearObservableCommutator.phase_pair_neg_swap_of_star_eq_neg P hPstar)
      A B hA hB hAP hBP
      (hilbertExpectationAt (E := E) psi A) (hilbertExpectationAt (E := E) psi B) psi

/-- The Robertson commutator bound obtained by dropping the nonnegative covariance square. -/
@[rep_depth operator]
theorem phaseCommutatorAt_sq_le_four_variance_mul
    (P : EndH) (psi : H₂) (A B : EndH)
    (hP : IsRealComplexStructure P.toLinearMap) (hPstar : star P = -P)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : A.comp P = P.comp A) (hBP : B.comp P = P.comp B) :
    (phaseCommutatorAt (E := E) P psi A B) ^ 2
      ≤ 4 * hilbertVarianceAt (E := E) psi A * hilbertVarianceAt (E := E) psi B := by
  have h := hilbertCovariance_sq_add_phaseCommutator_sq_div_four_le
    (E := E) P psi A B hP hPstar hA hB hAP hBP
  nlinarith [sq_nonneg (hilbertCovarianceAt (E := E) psi A B)]

/-- The existing canonical `K = Jε` phase gives the same centered commutator uncertainty law. -/
@[rep_depth operator]
theorem hilbertCovariance_sq_add_phaseAxisK_commutator_sq_div_four_le
    (psi : H₂) (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : IsPhaseLinear (E := E) A) (hBP : IsPhaseLinear (E := E) B) :
    (hilbertCovarianceAt (E := E) psi A B) ^ 2
        + (phaseCommutatorAt (E := E) (OperatorDictionary.phaseAxisK (E := E)) psi A B) ^ 2 / 4
      ≤ hilbertVarianceAt (E := E) psi A * hilbertVarianceAt (E := E) psi B := by
  simpa only [hilbertCovarianceAt, hilbertVarianceAt, centeredObservable_apply,
    phaseCommutatorAt, transportCommutator, PhaseLinearObservableCommutator.centeredVector,
    div_eq_mul_inv, one_mul, mul_comm] using
    PhaseObservableUncertainty.centered_robertson_schrodinger
      A B hA hB
      ((isPhaseLinear_iff_comp_complex_i A).mp hAP)
      ((isPhaseLinear_iff_comp_complex_i B).mp hBP)
      (hilbertExpectationAt (E := E) psi A) (hilbertExpectationAt (E := E) psi B) psi

end CenteredObservables

end InfoGeometry.Canonical.OperatorialUncertainty
