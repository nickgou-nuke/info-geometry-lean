/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Bilinear interpretation of the native real matrix adjoint split

This finite-dimensional layer distinguishes alternation from nondegeneracy.
It makes no assertion about closed differential forms on a manifold.
-/

namespace InfoGeometry.OperatorAlgebra.RealMatrixSplitGeometry

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The native matrix split transports through the bilinear-form linear equivalence. -/
theorem toBilin'_adjoint_split (M : Matrix n n ℝ) :
    M.toBilin' = (selfAdjointPart ℝ M : Matrix n n ℝ).toBilin' +
      (skewAdjointPart ℝ M : Matrix n n ℝ).toBilin' := by
  rw [← map_add, StarModule.selfAdjointPart_add_skewAdjointPart]

/-- The symmetric part gives a symmetric bilinear form, without a positivity premise. -/
theorem selfAdjointPart_toBilin'_isSymm (M : Matrix n n ℝ) :
    (selfAdjointPart ℝ M : Matrix n n ℝ).toBilin'.IsSymm := by
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  exact (selfAdjoint.isSelfAdjoint (x := selfAdjointPart ℝ M)).isHermitian.isSymm

/-- Transpose skew-symmetry becomes the expected interchange law for a real bilinear form. -/
theorem toBilin'_swap_of_transpose_eq_neg {Ω : Matrix n n ℝ}
    (hΩ : Ωᵀ = -Ω) (x y : n → ℝ) :
    Ω.toBilin' y x = -Ω.toBilin' x y := by
  simpa only [Matrix.toBilin'_apply', hΩ, Matrix.neg_mulVec, dotProduct_neg] using
    (Matrix.dotProduct_transpose_mulVec Ω x y).symm

/-- Over the reals, a transpose-skew matrix defines an alternating bilinear form. -/
theorem toBilin'_isAlt_of_transpose_eq_neg {Ω : Matrix n n ℝ}
    (hΩ : Ωᵀ = -Ω) : Ω.toBilin'.IsAlt := by
  intro x
  have h := toBilin'_swap_of_transpose_eq_neg hΩ x x
  exact CharZero.eq_neg_self_iff.mp h

/-- Alternation is automatic for the native skew-adjoint part over the reals. -/
theorem skewAdjointPart_toBilin'_isAlt (M : Matrix n n ℝ) :
    (skewAdjointPart ℝ M : Matrix n n ℝ).toBilin'.IsAlt := by
  apply toBilin'_isAlt_of_transpose_eq_neg
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using (skewAdjoint.star_val_eq (x := skewAdjointPart ℝ M))

/-- A nonzero determinant of a real skew matrix forces even dimension. -/
theorem even_card_of_transpose_eq_neg_det_ne_zero {Ω : Matrix n n ℝ}
    (hΩ : Ωᵀ = -Ω) (hdet : Ω.det ≠ 0) : Even (Fintype.card n) := by
  rcases Nat.even_or_odd (Fintype.card n) with heven | hodd
  · exact heven
  · have hsign : Ω.det = -Ω.det := by
      calc
        Ω.det = Ωᵀ.det := (Matrix.det_transpose Ω).symm
        _ = (-Ω).det := congrArg Matrix.det hΩ
        _ = -Ω.det := by rw [Matrix.det_neg, hodd.neg_one_pow, neg_one_mul]
    exact False.elim (hdet (CharZero.eq_neg_self_iff.mp hsign))

/-- The same parity obstruction expressed using the native bilinear nondegeneracy predicate. -/
theorem even_card_of_skew_toBilin'_nondegenerate {Ω : Matrix n n ℝ}
    (hΩ : Ωᵀ = -Ω) (hnd : Ω.toBilin'.Nondegenerate) : Even (Fintype.card n) := by
  exact even_card_of_transpose_eq_neg_det_ne_zero hΩ
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp hnd)

end InfoGeometry.OperatorAlgebra.RealMatrixSplitGeometry
