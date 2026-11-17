/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Real.Star
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Ring.Commute
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import InfoGeometry.OperatorAlgebra.WeightedAdjointCompatibility

/-!
# Raising a skew form and splitting a metric adjoint over the reals

The weighted adjoint is reused from `WeightedAdjointCompatibility`, with native
matrix units encoding invertibility. Symmetry of the weight is required for
involutivity. No positivity or complex-structure condition is inferred.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealMetricAdjoint

open Matrix
open WeightedAdjointCompatibility

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Raising the first index of a skew form gives a skew-adjoint operator for
an invertible symmetric form, including indefinite forms. -/
theorem raisedIndex_isSkewAdjoint {G Ω : Matrix n n ℝ}
    (hG : Gᵀ = G) (hdet : G.det ≠ 0) (hΩ : Ωᵀ = -Ω) :
    G.IsSkewAdjoint (G⁻¹ * Ω) := by
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  change (G⁻¹ * Ω)ᵀ * G = G * -(G⁻¹ * Ω)
  calc
    (G⁻¹ * Ω)ᵀ * G = -Ω := by
      rw [transpose_mul, transpose_nonsing_inv, hG, hΩ]
      exact nonsing_inv_mul_cancel_right G (-Ω) hunit
    _ = G * -(G⁻¹ * Ω) := by
      rw [mul_neg, mul_nonsing_inv_cancel_left G Ω hunit]

/-- Matrix form of skew-adjointness; the mixed multiplication order is fixed. -/
theorem raisedIndex_skew_identity {G Ω : Matrix n n ℝ}
    (hG : Gᵀ = G) (hdet : G.det ≠ 0) (hΩ : Ωᵀ = -Ω) :
    (G⁻¹ * Ω)ᵀ * G + G * (G⁻¹ * Ω) = 0 := by
  have h := raisedIndex_isSkewAdjoint hG hdet hΩ
  change (G⁻¹ * Ω)ᵀ * G = G * -(G⁻¹ * Ω) at h
  rw [mul_neg] at h
  exact add_eq_zero_iff_eq_neg.mpr h

/-- Raising an index recovers the skew form by evaluation of the original
bilinear form. This identity needs invertibility, but no symmetry. -/
theorem raisedIndex_toBilin' {G : Matrix n n ℝ} (hdet : G.det ≠ 0)
    (Ω : Matrix n n ℝ) (x y : n → ℝ) :
    Ω.toBilin' x y = G.toBilin' x ((G⁻¹ * Ω) *ᵥ y) := by
  rw [toBilin'_apply', toBilin'_apply', mulVec_mulVec,
    mul_nonsing_inv_cancel_left G Ω (isUnit_iff_ne_zero.mpr hdet)]

/-- The existing weighted adjoint has the usual inverse-transpose expression
when its carrier is a real matrix algebra. -/
theorem weightedAdjoint_matrix (w : (Matrix n n ℝ)ˣ) (M : Matrix n n ℝ) :
    adjoint w M = (w : Matrix n n ℝ)⁻¹ * Mᵀ * (w : Matrix n n ℝ) := by
  simp only [adjoint, coe_units_inv, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

/-- A nonzero determinant supplies the unit used by the existing weighted
adjoint, without introducing a second adjoint definition. -/
theorem weightedAdjoint_nonsingInvUnit (H M : Matrix n n ℝ) (hdet : H.det ≠ 0) :
    adjoint (H.nonsingInvUnit (isUnit_iff_ne_zero.mpr hdet)) M = H⁻¹ * Mᵀ * H := by
  change H⁻¹ * star M * H = H⁻¹ * Mᵀ * H
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- The native bilinear adjoint-pair predicate is satisfied by the weighted
adjoint. Symmetry of the weight is unnecessary for this particular identity. -/
theorem weightedAdjoint_isAdjointPair (w : (Matrix n n ℝ)ˣ) (M : Matrix n n ℝ) :
    (w : Matrix n n ℝ).IsAdjointPair (w : Matrix n n ℝ) M (adjoint w M) := by
  change Mᵀ * (w : Matrix n n ℝ) = (w : Matrix n n ℝ) * adjoint w M
  simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    using (mul_adjoint w M).symm

/-- The native adjoint-pair predicate uniquely specifies the adjoint for an
invertible metric matrix. -/
theorem weightedAdjoint_unique (w : (Matrix n n ℝ)ˣ) {M N : Matrix n n ℝ}
    (h : (w : Matrix n n ℝ).IsAdjointPair (w : Matrix n n ℝ) M N) :
    N = adjoint w M := by
  change Mᵀ * (w : Matrix n n ℝ) = (w : Matrix n n ℝ) * N at h
  have hstar : star M * (w : Matrix n n ℝ) = (w : Matrix n n ℝ) * N := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h
  rw [adjoint, mul_assoc, hstar]
  simp [← mul_assoc]

/-- Metric self-adjointness agrees with the native matrix predicate. -/
theorem isSelfAdjoint_iff_weightedAdjoint (w : (Matrix n n ℝ)ˣ) (M : Matrix n n ℝ) :
    (w : Matrix n n ℝ).IsSelfAdjoint M ↔ adjoint w M = M := by
  constructor
  · intro h
    exact (weightedAdjoint_unique w h).symm
  · intro h
    change (w : Matrix n n ℝ).IsAdjointPair (w : Matrix n n ℝ) M M
    simpa only [h] using weightedAdjoint_isAdjointPair w M

/-- Metric skew-adjointness agrees with the native matrix predicate. -/
theorem isSkewAdjoint_iff_weightedAdjoint (w : (Matrix n n ℝ)ˣ) (M : Matrix n n ℝ) :
    (w : Matrix n n ℝ).IsSkewAdjoint M ↔ adjoint w M = -M := by
  constructor
  · intro h
    exact (weightedAdjoint_unique w h).symm
  · intro h
    change (w : Matrix n n ℝ).IsAdjointPair (w : Matrix n n ℝ) M (-M)
    simpa only [h] using weightedAdjoint_isAdjointPair w M

/-- The weighted adjoint is additive on the full matrix algebra. -/
theorem weightedAdjoint_add (w : (Matrix n n ℝ)ˣ) (M N : Matrix n n ℝ) :
    adjoint w (M + N) = adjoint w M + adjoint w N := by
  simp only [adjoint, star_add, mul_add, add_mul]

/-- The weighted adjoint respects subtraction. -/
theorem weightedAdjoint_sub (w : (Matrix n n ℝ)ˣ) (M N : Matrix n n ℝ) :
    adjoint w (M - N) = adjoint w M - adjoint w N := by
  simp only [adjoint, star_sub, mul_sub, sub_mul]

/-- The weighted adjoint is real-linear. -/
theorem weightedAdjoint_smul (w : (Matrix n n ℝ)ˣ) (r : ℝ) (M : Matrix n n ℝ) :
    adjoint w (r • M) = r • adjoint w M := by
  simp only [adjoint, star_smul, star_trivial, mul_smul_comm, smul_mul_assoc]

/-- A symmetric metric makes the existing weighted adjoint an involution. -/
theorem weightedAdjoint_involutive (w : (Matrix n n ℝ)ˣ)
    (hw : (w : Matrix n n ℝ)ᵀ = (w : Matrix n n ℝ)) (M : Matrix n n ℝ) :
    adjoint w (adjoint w M) = M := by
  apply adjoint_involutive w
  simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hw

/-- The metric self-adjoint part has eigenvalue `+1` for the weighted adjoint. -/
theorem weightedAdjoint_symmetric_part (w : (Matrix n n ℝ)ˣ)
    (hw : (w : Matrix n n ℝ)ᵀ = (w : Matrix n n ℝ)) (M : Matrix n n ℝ) :
    adjoint w ((1 / 2 : ℝ) • (M + adjoint w M)) =
      (1 / 2 : ℝ) • (M + adjoint w M) := by
  rw [weightedAdjoint_smul, weightedAdjoint_add, weightedAdjoint_involutive w hw]
  rw [add_comm]

/-- The metric skew-adjoint part has eigenvalue `-1` for the weighted adjoint. -/
theorem weightedAdjoint_skew_part (w : (Matrix n n ℝ)ˣ)
    (hw : (w : Matrix n n ℝ)ᵀ = (w : Matrix n n ℝ)) (M : Matrix n n ℝ) :
    adjoint w ((1 / 2 : ℝ) • (M - adjoint w M)) =
      -((1 / 2 : ℝ) • (M - adjoint w M)) := by
  rw [weightedAdjoint_smul, weightedAdjoint_sub, weightedAdjoint_involutive w hw]
  rw [← smul_neg, neg_sub]

/-- The two metric parts reconstruct every matrix, without a commutation
assumption. -/
theorem weightedAdjoint_split (w : (Matrix n n ℝ)ˣ) (M : Matrix n n ℝ) :
    (1 / 2 : ℝ) • (M + adjoint w M) +
      (1 / 2 : ℝ) • (M - adjoint w M) = M := by
  rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ M, smul_smul]
  norm_num

/-- Uniqueness recovers the metric self-adjoint summand from any decomposition
into the two eigenspaces of the weighted adjoint. -/
theorem weightedAdjoint_symmetric_part_unique (w : (Matrix n n ℝ)ˣ)
    {M S A : Matrix n n ℝ} (hS : adjoint w S = S) (hA : adjoint w A = -A)
    (hM : S + A = M) :
    (1 / 2 : ℝ) • (M + adjoint w M) = S := by
  rw [← hM, weightedAdjoint_add, hS, hA]
  have heq : S + A + (S + -A) = S + S := by abel
  rw [heq, ← two_smul ℝ S, smul_smul]
  norm_num

/-- Uniqueness also recovers the metric skew-adjoint summand. -/
theorem weightedAdjoint_skew_part_unique (w : (Matrix n n ℝ)ˣ)
    {M S A : Matrix n n ℝ} (hS : adjoint w S = S) (hA : adjoint w A = -A)
    (hM : S + A = M) :
    (1 / 2 : ℝ) • (M - adjoint w M) = A := by
  rw [← hM, weightedAdjoint_add, hS, hA]
  have heq : S + A - (S + -A) = A + A := by abel
  rw [heq, ← two_smul ℝ A, smul_smul]
  norm_num

/-- On a full real matrix algebra, equality of weighted adjoints determines
the metric weight up to a scalar multiple. The statement also covers the
zero-dimensional matrix algebra. -/
theorem weightedAdjoint_eq_iff_scalar_multiple
    (w z : (Matrix n n ℝ)ˣ) :
    adjoint w = adjoint z ↔
      ∃ c : ℝ, (↑w : Matrix n n ℝ) = c • (↑z : Matrix n n ℝ) := by
  constructor
  · intro h
    have hcomm := (adjoint_eq_iff_relative_central w z).mp h
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
      (fun i j _ => hcomm (Matrix.single i j 1))
    refine ⟨c, ?_⟩
    calc
      (↑w : Matrix n n ℝ) =
          ((↑w : Matrix n n ℝ) * (↑z⁻¹ : Matrix n n ℝ)) * ↑z := by
        simp [mul_assoc]
      _ = Matrix.scalar n c * ↑z := by rw [← hc]
      _ = c • (↑z : Matrix n n ℝ) := by
        rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  · rintro ⟨c, hc⟩
    apply (adjoint_eq_iff_relative_central w z).mpr
    intro x
    change x * ((↑w : Matrix n n ℝ) * (↑z⁻¹ : Matrix n n ℝ)) =
      ((↑w : Matrix n n ℝ) * (↑z⁻¹ : Matrix n n ℝ)) * x
    simp [hc]

/-- In positive dimension, an invertible weight cannot be the zero multiple
of another weight. No positivity or symmetry assumption is needed. -/
theorem weightedAdjoint_eq_iff_nonzero_scalar_multiple [Nonempty n]
    (w z : (Matrix n n ℝ)ˣ) :
    adjoint w = adjoint z ↔
      ∃ c : ℝ, c ≠ 0 ∧ (↑w : Matrix n n ℝ) = c • (↑z : Matrix n n ℝ) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (weightedAdjoint_eq_iff_scalar_multiple w z).mp h
    refine ⟨c, ?_, hc⟩
    intro hzero
    rw [hzero, zero_smul] at hc
    exact w.ne_zero hc
  · rintro ⟨c, _, hc⟩
    exact (weightedAdjoint_eq_iff_scalar_multiple w z).mpr ⟨c, hc⟩

/-- Normalizing both real metric weights to square to one leaves exactly a
global sign ambiguity. Symmetry is not needed for this recovery statement;
the existing involutivity theorem uses it as a sufficient hypothesis. -/
theorem weightedAdjoint_eq_iff_eq_or_neg [Nonempty n]
    (w z : (Matrix n n ℝ)ˣ)
    (hw : (↑w : Matrix n n ℝ) * (↑w : Matrix n n ℝ) = 1)
    (hz : (↑z : Matrix n n ℝ) * (↑z : Matrix n n ℝ) = 1) :
    adjoint w = adjoint z ↔
      (↑w : Matrix n n ℝ) = ↑z ∨ (↑w : Matrix n n ℝ) = -(↑z : Matrix n n ℝ) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (weightedAdjoint_eq_iff_scalar_multiple w z).mp h
    have hs : (c * c) • (1 : Matrix n n ℝ) = 1 := by
      calc
        (c * c) • (1 : Matrix n n ℝ) =
            (c • (↑z : Matrix n n ℝ)) * (c • (↑z : Matrix n n ℝ)) := by
          simp [smul_smul, hz]
        _ = (↑w : Matrix n n ℝ) * (↑w : Matrix n n ℝ) := by rw [← hc]
        _ = 1 := hw
    obtain ⟨i⟩ := ‹Nonempty n›
    have hcc : c * c = 1 := by
      have hentry := congrArg (fun M : Matrix n n ℝ => M i i) hs
      simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        using hentry
    rcases mul_self_eq_one_iff.mp hcc with hpos | hneg
    · left
      simpa [hpos] using hc
    · right
      simpa [hneg] using hc
  · intro h
    apply (weightedAdjoint_eq_iff_scalar_multiple w z).mpr
    rcases h with hpos | hneg
    · exact ⟨1, by simpa using hpos⟩
    · exact ⟨-1, by simpa using hneg⟩

end InfoGeometry.OperatorAlgebra.RealMetricAdjoint
