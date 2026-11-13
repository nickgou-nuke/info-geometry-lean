/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Star.Module
import Mathlib.Basic.Real.Star
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.NoncommRing

/-!
# Real matrix splitting and the normality defect

The two parts are Mathlib's real-linear `selfAdjointPart` and
`skewAdjointPart`. Their carrier is the full real matrix algebra. The
normality defect retains both ordered mixed products; no commutation or
nondegeneracy is assumed. Congruence, the transformation law for bilinear
forms, preserves the split even for singular change-of-coordinate matrices.
-/

namespace InfoGeometry.OperatorAlgebra.RealMatrixSplit

open Matrix

variable {n : Type*}

/-- Over the reals the native self-adjoint part is the symmetric half. -/
theorem selfAdjointPart_eq_half (M : Matrix n n ℝ) :
    (selfAdjointPart ℝ M : Matrix n n ℝ) = (1 / 2 : ℝ) • (M + M.transpose) := by
  simp only [selfAdjointPart_apply_coe, invOf_eq_inv, one_div,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Over the reals the native skew-adjoint part is the antisymmetric half. -/
theorem skewAdjointPart_eq_half (M : Matrix n n ℝ) :
    (skewAdjointPart ℝ M : Matrix n n ℝ) = (1 / 2 : ℝ) • (M - M.transpose) := by
  simp only [skewAdjointPart_apply_coe, invOf_eq_inv, one_div,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

section Multiplication

variable [Fintype n] [DecidableEq n]

/-- The square expansion keeps the order of both mixed matrix products. -/
theorem square_of_split {M G Ω : Matrix n n ℝ} (hM : G + Ω = M) :
    M * M = G * G + G * Ω + Ω * G + Ω * Ω := by
  rw [← hM]
  noncomm_ring

/-- Exact normality defect for any symmetric/skew decomposition. -/
theorem transpose_normal_defect_of_split {M G Ω : Matrix n n ℝ}
    (hG : G.transpose = G) (hΩ : Ω.transpose = -Ω) (hM : G + Ω = M) :
    M.transpose * M - M * M.transpose = (2 : ℝ) • (G * Ω - Ω * G) := by
  rw [← hM, Matrix.transpose_add, hG, hΩ, two_smul]
  noncomm_ring

/-- The native real split measures exactly the failure of transpose-normality. -/
theorem transpose_normal_defect (M : Matrix n n ℝ) :
    M.transpose * M - M * M.transpose =
      (2 : ℝ) • ((selfAdjointPart ℝ M : Matrix n n ℝ) *
        (skewAdjointPart ℝ M : Matrix n n ℝ) -
        (skewAdjointPart ℝ M : Matrix n n ℝ) *
        (selfAdjointPart ℝ M : Matrix n n ℝ)) := by
  apply transpose_normal_defect_of_split
  · simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
      using selfAdjoint.isSelfAdjoint (x := selfAdjointPart ℝ M)
  · simpa only [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using (skewAdjointPart ℝ M).property
  · exact StarModule.selfAdjointPart_add_skewAdjointPart ℝ M

/-- Normality is equivalent to commutation of the two native real parts. -/
theorem isStarNormal_iff_parts_commute (M : Matrix n n ℝ) :
    IsStarNormal M ↔ Commute (selfAdjointPart ℝ M : Matrix n n ℝ)
      (skewAdjointPart ℝ M : Matrix n n ℝ) := by
  rw [isStarNormal_iff, commute_iff_eq, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← sub_eq_zero,
    transpose_normal_defect, smul_eq_zero_iff_right (two_ne_zero : (2 : ℝ) ≠ 0),
    sub_eq_zero, commute_iff_eq]

/-- Congruence transports the symmetric bilinear-form component. -/
theorem selfAdjointPart_congruence (M P : Matrix n n ℝ) :
    (selfAdjointPart ℝ (P.transpose * M * P) : Matrix n n ℝ) =
      P.transpose * (selfAdjointPart ℝ M : Matrix n n ℝ) * P := by
  simp only [selfAdjointPart_eq_half, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, mul_add, add_mul, smul_add, smul_mul_assoc, mul_smul_comm]

/-- Congruence transports the skew bilinear-form component. -/
theorem skewAdjointPart_congruence (M P : Matrix n n ℝ) :
    (skewAdjointPart ℝ (P.transpose * M * P) : Matrix n n ℝ) =
      P.transpose * (skewAdjointPart ℝ M : Matrix n n ℝ) * P := by
  simp only [skewAdjointPart_eq_half, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, mul_sub, sub_mul, smul_sub, smul_mul_assoc, mul_smul_comm]

end Multiplication

end InfoGeometry.OperatorAlgebra.RealMatrixSplit
