import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
--- AUDIT PROTOCOL MAP ---

BUCKET 1: CLOSED FINITE THEOREMS:
  - det_conj_eq_det
  - det_transpose_eq
  - det_diagonal_eq_prod
  - mul_adjugate_eq_det_smul_one
  - adjugate_mul_eq_det_smul_one
  - det_one_add_mul_comm_eq
  - det_fin_two_eq
  - det_fromBlocks₂₂_eq (Transparent Alias)

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES:
  - None. All bridged properties rely strictly on the foundational 
    commutative ring and fintype structures provided natively by Mathlib.

BUCKET 3: OPEN CLOSURE DEBT:
  - None.
--------------------------
-/

namespace InfoGeometry.Canonical.DeterminantBasicBridge

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- 
Conjugation invariance of the determinant. 
Provides a direct owner-facing alias for determinant under similarity.
-/
theorem det_conj_eq_det (A : Matrix n n R) (U : (Matrix n n R)ˣ) :
    det ((U : Matrix n n R) * A * (↑U⁻¹ : Matrix n n R)) = det A := by
  rw [Matrix.det_mul, Matrix.det_mul]
  have h : det (U : Matrix n n R) * det ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) = 1 := by
    rw [← Matrix.det_mul, U.mul_inv, Matrix.det_one]
  calc
    det (U : Matrix n n R) * det A * det ((↑U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) =
      det A * (det (U : Matrix n n R) * det ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)) := by ring
    _ = det A * 1 := by rw [h]
    _ = det A := by simp

/-- 
Transposition invariance of the determinant. 
Provides a direct owner-facing alias for `Matrix.det_transpose`.
-/
theorem det_transpose_eq (A : Matrix n n R) :
    det Aᵀ = det A :=
  Matrix.det_transpose A

/-- 
Determinant of a diagonal matrix is the product of its entries. 
Provides a direct owner-facing alias for `Matrix.det_diagonal`.
-/
theorem det_diagonal_eq_prod (d : n → R) :
    det (diagonal d) = ∏ i, d i :=
  det_diagonal

/-- 
Right multiplication by the adjugate yields the determinant scalar matrix. 
Provides a direct owner-facing alias for `Matrix.mul_adjugate`.
-/
theorem mul_adjugate_eq_det_smul_one (A : Matrix n n R) :
    A * adjugate A = det A • (1 : Matrix n n R) :=
  Matrix.mul_adjugate A

/-- 
Left multiplication by the adjugate yields the determinant scalar matrix. 
Provides a direct owner-facing alias for `Matrix.adjugate_mul`.
-/
theorem adjugate_mul_eq_det_smul_one (A : Matrix n n R) :
    adjugate A * A = det A • (1 : Matrix n n R) :=
  Matrix.adjugate_mul A

/--
Sylvester's determinant identity for commuting products of rectangular matrices.
Provides a direct owner-facing alias for `Matrix.det_one_add_mul_comm`.
-/
theorem det_one_add_mul_comm_eq {m : Type*} [Fintype m] [DecidableEq m] 
    (A : Matrix n m R) (B : Matrix m n R) :
    det ((1 : Matrix n n R) + A * B) = det ((1 : Matrix m m R) + B * A) :=
  Matrix.det_one_add_mul_comm A B

/--
Explicit determinant formula for 2x2 matrices.
Provides a direct owner-facing alias for `Matrix.det_fin_two`.
-/
theorem det_fin_two_eq (A : Matrix (Fin 2) (Fin 2) R) :
    det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 :=
  Matrix.det_fin_two A

/--
Schur complement determinant factorization for block matrices.
Provides a direct owner-facing alias for `Matrix.det_fromBlocks₂₂`.
-/
theorem det_fromBlocks₂₂_eq
    {m : Type*} [Fintype m] [DecidableEq m] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (D : Matrix n n R) [Invertible D] :
    det (Matrix.fromBlocks A B C D) = det D * det (A - B * ⅟D * C) := by
  simpa using (Matrix.det_fromBlocks₂₂ A B C D)

end InfoGeometry.Canonical.DeterminantBasicBridge
