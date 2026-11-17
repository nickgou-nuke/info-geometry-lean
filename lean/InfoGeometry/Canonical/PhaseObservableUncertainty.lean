/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.PhaseLinearObservableCommutator
import InfoGeometry.Krein.InternalPhaseGram

/-!
# Commutator uncertainty for real phase-preserving observables

The low-level Bessel inequality supplies the positive Gram bound for any
norm-preserving skew phase on the doubled Hilbert carrier. The canonical
phase APIs remain specializations of that general bound.
`PhaseLinearObservableCommutator` identifies its phase term with the
expectation of the actual ordered operator commutator.  Thus this owner
derives the Robertson--Schrödinger and Robertson bounds without assuming a
Cramér--Rao inequality or a canonical commutation relation.

The arbitrary-shift bounds require no state normalization.  The final
second-moment identity records exactly where unit normalization is needed
to interpret the centered squared norm as a variance.  These are Hilbert
covariances; no Lorentzian covariance metric or spacetime dynamics is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.PhaseObservableUncertainty

open InfoGeometry.Krein
open InfoGeometry.Krein.PhaseLinearObservableCommutator
open scoped InnerProductSpace

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => DoubledEnd E
local notation "Iop" => complex_i (E := E)

/-- The full arbitrary-shift bound for any norm-preserving real phase
with skew pairing. The phase square law is not required separately. -/
theorem centered_robertson_schrodinger_of_phase
    (P : EndH)
    (hPnorm : ∀ x : H₂, ‖P x‖ = ‖x‖)
    (hPskew : ∀ x y : H₂, ⟪P x, y⟫_ℝ = -⟪P y, x⟫_ℝ)
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : A.comp P = P.comp A) (hBP : B.comp P = P.comp B)
    (a b : ℝ) (ψ : H₂) :
    (⟪centeredVector A a ψ, centeredVector B b ψ⟫_ℝ) ^ 2 +
        (1 / 4 : ℝ) * (⟪P ψ, (A.comp B - B.comp A) ψ⟫_ℝ) ^ 2 ≤
      ‖centeredVector A a ψ‖ ^ 2 * ‖centeredVector B b ψ‖ ^ 2 := by
  have hphase := twice_centered_phase_pair_eq_commutator_of_phase
    P hPskew A B hA hB hAP hBP a b ψ
  have harea := InternalPhaseGram.inner_sq_add_operator_inner_sq_le P hPnorm
    (fun x => InternalPhaseGram.phase_pair_self_zero_of_neg_swap P hPskew x)
    (centeredVector A a ψ) (centeredVector B b ψ)
  calc
    (⟪centeredVector A a ψ, centeredVector B b ψ⟫_ℝ) ^ 2 +
        (1 / 4 : ℝ) * (⟪P ψ, (A.comp B - B.comp A) ψ⟫_ℝ) ^ 2 =
      (⟪centeredVector A a ψ, centeredVector B b ψ⟫_ℝ) ^ 2 +
        (⟪P (centeredVector A a ψ), centeredVector B b ψ⟫_ℝ) ^ 2 := by
          rw [← hphase]
          ring
    _ ≤ ‖centeredVector A a ψ‖ ^ 2 * ‖centeredVector B b ψ‖ ^ 2 := harea

/-- The Robertson bound for arbitrary real shifts and an arbitrary
norm-preserving skew phase. -/
theorem centered_robertson_of_phase
    (P : EndH)
    (hPnorm : ∀ x : H₂, ‖P x‖ = ‖x‖)
    (hPskew : ∀ x y : H₂, ⟪P x, y⟫_ℝ = -⟪P y, x⟫_ℝ)
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAP : A.comp P = P.comp A) (hBP : B.comp P = P.comp B)
    (a b : ℝ) (ψ : H₂) :
    (1 / 4 : ℝ) * (⟪P ψ, (A.comp B - B.comp A) ψ⟫_ℝ) ^ 2 ≤
      ‖centeredVector A a ψ‖ ^ 2 * ‖centeredVector B b ψ‖ ^ 2 := by
  have h := centered_robertson_schrodinger_of_phase
    P hPnorm hPskew A B hA hB hAP hBP a b ψ
  have hcov := sq_nonneg (⟪centeredVector A a ψ, centeredVector B b ψ⟫_ℝ)
  linarith

/-- The full covariance-plus-commutator uncertainty bound for actual
self-adjoint real observables preserving the internal phase. -/
theorem centered_robertson_schrodinger
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAI : A.comp Iop = (Iop).comp A)
    (hBI : B.comp Iop = (Iop).comp B)
    (a b : ℝ) (ψ : H₂) :
    (⟪centeredVector A a ψ, centeredVector B b ψ⟫_ℝ) ^ 2 +
        (1 / 4 : ℝ) * (⟪Iop ψ, (A.comp B - B.comp A) ψ⟫_ℝ) ^ 2 ≤
      ‖centeredVector A a ψ‖ ^ 2 * ‖centeredVector B b ψ‖ ^ 2 := by
  exact centered_robertson_schrodinger_of_phase Iop
    (fun x => complex_i_norm x) (fun x y => InternalPhaseGram.phase_pair_neg_swap x y)
    A B hA hB hAI hBI a b ψ

/-- Dropping the nonnegative real covariance square gives the Robertson
commutator lower bound. -/
theorem centered_robertson
    (A B : EndH) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAI : A.comp Iop = (Iop).comp A)
    (hBI : B.comp Iop = (Iop).comp B)
    (a b : ℝ) (ψ : H₂) :
    (1 / 4 : ℝ) * (⟪Iop ψ, (A.comp B - B.comp A) ψ⟫_ℝ) ^ 2 ≤
      ‖centeredVector A a ψ‖ ^ 2 * ‖centeredVector B b ψ‖ ^ 2 := by
  exact centered_robertson_of_phase Iop
    (fun x => complex_i_norm x) (fun x y => InternalPhaseGram.phase_pair_neg_swap x y)
    A B hA hB hAI hBI a b ψ

/-- With a unit state and its actual mean, the centered Hilbert squared
norm is the second moment minus the squared mean. -/
theorem centered_norm_sq_eq_second_moment_sub_mean_sq
    (A : EndH) (hA : IsSelfAdjoint A) (ψ : H₂)
    (hψ : ⟪ψ, ψ⟫_ℝ = 1) :
    ‖centeredVector A (⟪ψ, A ψ⟫_ℝ) ψ‖ ^ 2 =
      ⟪ψ, (A.comp A) ψ⟫_ℝ - (⟪ψ, A ψ⟫_ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [centeredVector, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hψ]
  have hsecond : ⟪A ψ, A ψ⟫_ℝ = ⟪ψ, (A.comp A) ψ⟫_ℝ :=
    hA.isSymmetric ψ (A ψ)
  rw [hsecond, real_inner_comm (A ψ) ψ]
  ring

end InfoGeometry.Canonical.PhaseObservableUncertainty
