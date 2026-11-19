/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGeometry.Projective.QGT
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Differential of the overlap of normalized Hilbert states

This extends the existing `NormalizedState` and `projOrth` owners. The ray
operator is Mathlib's `InnerProductSpace.rankOne`; no new projector or state
carrier is introduced.

For differentiable normalized curves, the overlap derivative splits into the
difference of the two vertical connection coefficients times the overlap,
plus two horizontal terms. Normalization implies the tangent identity used
in the proof. Division by the overlap is restricted to its nonzero locus.

The statements concern real-parameter Hilbert-space calculus. They do not
identify a field-theoretic current, choose a logarithm branch, construct a
determinant line bundle, or compute an anomaly coefficient.
-/

noncomputable section

namespace InfoGeometry.QuantumGeometry.Projective

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The owned horizontal vector is the native complementary ray operator
applied to the operator-generated velocity. -/
theorem projOrth_eq_complement_rankOne_apply
    (ψ : NormalizedState H) (X : H →L[ℂ] H) :
    projOrth ψ X =
      ((1 : H →L[ℂ] H) - InnerProductSpace.rankOne ℂ ψ.vec ψ.vec) (X ψ.vec) :=
  rfl

/-- Algebraic overlap variation with the left tangent condition explicit.
Only scalar coefficients commute; the complementary operators keep their
specified action on the two velocity vectors. -/
theorem overlap_tangent_split
    (ψ φ : NormalizedState H) (dψ dφ : H)
    (hψ : ⟪dψ, ψ.vec⟫_ℂ = -⟪ψ.vec, dψ⟫_ℂ) :
    ⟪ψ.vec, dφ⟫_ℂ + ⟪dψ, φ.vec⟫_ℂ =
      (⟪φ.vec, dφ⟫_ℂ - ⟪ψ.vec, dψ⟫_ℂ) * ⟪ψ.vec, φ.vec⟫_ℂ +
        ⟪((1 : H →L[ℂ] H) - InnerProductSpace.rankOne ℂ ψ.vec ψ.vec) dψ,
          φ.vec⟫_ℂ +
        ⟪ψ.vec,
          ((1 : H →L[ℂ] H) - InnerProductSpace.rankOne ℂ φ.vec φ.vec) dφ⟫_ℂ := by
  change ⟪ψ.vec, dφ⟫_ℂ + ⟪dψ, φ.vec⟫_ℂ =
    (⟪φ.vec, dφ⟫_ℂ - ⟪ψ.vec, dψ⟫_ℂ) * ⟪ψ.vec, φ.vec⟫_ℂ +
      ⟪dψ - ⟪ψ.vec, dψ⟫_ℂ • ψ.vec, φ.vec⟫_ℂ +
      ⟪ψ.vec, dφ - ⟪φ.vec, dφ⟫_ℂ • φ.vec⟫_ℂ
  rw [inner_sub_left, inner_smul_left, inner_sub_right, inner_smul_right]
  have hconj : starRingEnd ℂ (⟪ψ.vec, dψ⟫_ℂ) = ⟪dψ, ψ.vec⟫_ℂ :=
    inner_conj_symm dψ ψ.vec
  rw [hconj, hψ]
  ring

section RealDerivatives

variable [NormedSpace ℝ H]

/-- Differentiating the normalization law gives the purely imaginary vertical
coefficient; this tangent condition is derived, not assumed. -/
theorem normalizedState_derivative_inner_eq_neg
    {ψ : ℝ → NormalizedState H} {dψ : H} {t : ℝ}
    (hψ : HasDerivAt (fun s => (ψ s).vec) dψ t) :
    ⟪dψ, (ψ t).vec⟫_ℂ = -⟪(ψ t).vec, dψ⟫_ℂ := by
  have hnorm : HasDerivAt (fun _ : ℝ => (1 : ℂ))
      (⟪(ψ t).vec, dψ⟫_ℂ + ⟪dψ, (ψ t).vec⟫_ℂ) t := by
    simpa only [NormalizedState.norm_sq] using hψ.inner ℂ hψ
  exact eq_neg_of_add_eq_zero_right (hnorm.unique (hasDerivAt_const t (1 : ℂ)))

/-- The actual derivative of the overlap splits into vertical and horizontal
terms on arbitrary complex inner product spaces. No nonzero-overlap premise
is needed before taking a quotient. -/
theorem hasDerivAt_overlap_horizontal_split
    {ψ φ : ℝ → NormalizedState H} {dψ dφ : H} {t : ℝ}
    (hψ : HasDerivAt (fun s => (ψ s).vec) dψ t)
    (hφ : HasDerivAt (fun s => (φ s).vec) dφ t) :
    HasDerivAt (fun s => ⟪(ψ s).vec, (φ s).vec⟫_ℂ)
      ((⟪(φ t).vec, dφ⟫_ℂ - ⟪(ψ t).vec, dψ⟫_ℂ) *
          ⟪(ψ t).vec, (φ t).vec⟫_ℂ +
        ⟪((1 : H →L[ℂ] H) -
          InnerProductSpace.rankOne ℂ (ψ t).vec (ψ t).vec) dψ, (φ t).vec⟫_ℂ +
        ⟪(ψ t).vec, ((1 : H →L[ℂ] H) -
          InnerProductSpace.rankOne ℂ (φ t).vec (φ t).vec) dφ⟫_ℂ) t := by
  exact (hψ.inner ℂ hφ).congr_deriv
    (overlap_tangent_split (ψ t) (φ t) dψ dφ
      (normalizedState_derivative_inner_eq_neg hψ))

/-- On the nonzero-overlap locus, the logarithmic derivative `z'/z` is the
connection difference plus the normalized horizontal numerator. This does
not assert a globally defined complex logarithm. -/
theorem logarithmic_overlap_derivative_split
    {ψ φ : ℝ → NormalizedState H} {dψ dφ : H} {t : ℝ}
    (hψ : HasDerivAt (fun s => (ψ s).vec) dψ t)
    (hφ : HasDerivAt (fun s => (φ s).vec) dφ t)
    (hz : ⟪(ψ t).vec, (φ t).vec⟫_ℂ ≠ 0) :
    deriv (fun s => ⟪(ψ s).vec, (φ s).vec⟫_ℂ) t /
        ⟪(ψ t).vec, (φ t).vec⟫_ℂ =
      ⟪(φ t).vec, dφ⟫_ℂ - ⟪(ψ t).vec, dψ⟫_ℂ +
        (⟪((1 : H →L[ℂ] H) -
            InnerProductSpace.rankOne ℂ (ψ t).vec (ψ t).vec) dψ, (φ t).vec⟫_ℂ +
          ⟪(ψ t).vec, ((1 : H →L[ℂ] H) -
            InnerProductSpace.rankOne ℂ (φ t).vec (φ t).vec) dφ⟫_ℂ) /
          ⟪(ψ t).vec, (φ t).vec⟫_ℂ := by
  rw [(hasDerivAt_overlap_horizontal_split hψ hφ).deriv]
  field_simp [hz] <;> ring

/-- Operator-generated velocities read directly through the existing QGT
horizontal projection, with no new horizontal-vector API. -/
theorem hasDerivAt_overlap_projOrth_split
    {ψ φ : ℝ → NormalizedState H} {t : ℝ} (X Y : H →L[ℂ] H)
    (hψ : HasDerivAt (fun s => (ψ s).vec) (X (ψ t).vec) t)
    (hφ : HasDerivAt (fun s => (φ s).vec) (Y (φ t).vec) t) :
    HasDerivAt (fun s => ⟪(ψ s).vec, (φ s).vec⟫_ℂ)
      ((⟪(φ t).vec, Y (φ t).vec⟫_ℂ - ⟪(ψ t).vec, X (ψ t).vec⟫_ℂ) *
          ⟪(ψ t).vec, (φ t).vec⟫_ℂ +
        ⟪projOrth (ψ t) X, (φ t).vec⟫_ℂ +
        ⟪(ψ t).vec, projOrth (φ t) Y⟫_ℂ) t := by
  exact hasDerivAt_overlap_horizontal_split hψ hφ

end RealDerivatives

end InfoGeometry.QuantumGeometry.Projective
