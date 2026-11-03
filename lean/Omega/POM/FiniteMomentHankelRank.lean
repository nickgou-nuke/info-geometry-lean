/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Finite Prony moment Hankel matrices

The weighted moment Hankel matrix is a Vandermonde Gram matrix. Distinct
support and nonzero weights imply nonzero determinant and full rank over a
field.
-/

namespace Omega.POM

open Matrix

variable {R : Type*} [Field R] {n : ℕ}

/-- The finite weighted moment Hankel matrix. -/
def finiteMomentHankel (x w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j ↦ ∑ k : Fin n, w k * x k ^ (i.1 + j.1)

/-- The moment Hankel matrix is a Vandermonde Gram matrix. -/
theorem finiteMomentHankel_eq_vandermonde_gram (x w : Fin n → R) :
    finiteMomentHankel x w = ((Matrix.vandermonde x)ᵀ *
      Matrix.diagonal w) * Matrix.vandermonde x := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [finiteMomentHankel, Matrix.mul_diagonal,
    Matrix.transpose_apply, Matrix.vandermonde_apply, pow_add]
  apply Finset.sum_congr rfl
  intro k hk
  ring_nf

/-- Distinct nodes and nonzero weights give a nonzero Hankel determinant. -/
theorem finiteMomentHankel_det_ne_zero (x w : Fin n → R)
    (hx : Function.Injective x) (hw : ∀ i, w i ≠ 0) :
    (finiteMomentHankel x w).det ≠ 0 := by
  rw [finiteMomentHankel_eq_vandermonde_gram, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal]
  have hV : (Matrix.vandermonde x).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff).2 hx
  have hD : (∏ i : Fin n, w i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ hw i
  exact mul_ne_zero (mul_ne_zero hV hD) hV

/-- The finite weighted moment Hankel matrix has full rank. -/
theorem finiteMomentHankel_rank (x w : Fin n → R)
    (hx : Function.Injective x) (hw : ∀ i, w i ≠ 0) :
    (finiteMomentHankel x w).rank = n := by
  simpa using Matrix.rank_of_det_ne_zero (finiteMomentHankel_det_ne_zero x w hx hw)

end Omega.POM
