/-
InfoGeometry/OperatorAlgebra/VerifiedDeterminant.lean

The individuation of the determinant.

This module kills the shadow:

  is_det_invariant : Prop

by proving constructively, for finite matrices,

  det(U A U^{-1}) = det(A)

from determinant multiplicativity and an explicit inverse law.

No vacuous determinant-invariance certificate is used.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.IndividuatedCasimir

noncomputable section

namespace InfoGeometry.OperatorAlgebra.VerifiedDeterminant

open InfoGeometry.OperatorAlgebra.IndividuatedCasimir
open scoped Matrix

/-! ## 1. Finite determinant conjugation invariance -/

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/--
Finite matrix determinant is invariant under conjugation.

The proof is purely multiplicative:

`det(U A U⁻¹) = det(U) det(A) det(U⁻¹) = det(A)`.
-/
theorem matrix_det_conjugation_invariant
    (A U U_inv : Matrix n n R)
    (h_right : U * U_inv = 1) :
    Matrix.det (U * A * U_inv) = Matrix.det A := by
  have hdet_right :
      Matrix.det U * Matrix.det U_inv = 1 := by
    have h := congrArg Matrix.det h_right
    simpa [Matrix.det_mul] using h
  calc
    Matrix.det (U * A * U_inv)
        = Matrix.det (U * A) * Matrix.det U_inv := by
            rw [Matrix.det_mul]
    _ = (Matrix.det U * Matrix.det A) * Matrix.det U_inv := by
            rw [Matrix.det_mul]
    _ = Matrix.det A * (Matrix.det U * Matrix.det U_inv) := by
            ring
    _ = Matrix.det A * 1 := by
            rw [hdet_right]
    _ = Matrix.det A := by
            rw [mul_one]

/--
Determinant invariance for an `InvertibleTransport` of a finite matrix algebra.
-/
theorem matrix_det_invariant_under_transport
    (A : Matrix n n R)
    (U : InvertibleTransport (Matrix n n R)) :
    Matrix.det (U.conjugate A) = Matrix.det A := by
  dsimp [InvertibleTransport.conjugate]
  exact matrix_det_conjugation_invariant A U.val U.inv U.val_inv

/-! ## 2. Real finite matrix specialization -/

/--
Verified real determinant on `Fin n` matrices.
-/
def realMatrixDeterminant
    (n : ℕ) : Matrix (Fin n) (Fin n) ℝ → ℝ :=
  Matrix.det

/--
Real finite matrix determinant is invariant under invertible conjugation.
-/
theorem real_matrix_det_invariant_under_transport
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (U : InvertibleTransport (Matrix (Fin n) (Fin n) ℝ)) :
    Matrix.det (U.conjugate A) = Matrix.det A :=
  matrix_det_invariant_under_transport A U

end InfoGeometry.OperatorAlgebra.VerifiedDeterminant
