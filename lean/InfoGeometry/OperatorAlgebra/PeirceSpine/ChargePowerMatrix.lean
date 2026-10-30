/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteMatrixNoncommutativity
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Integer coefficient matrix for the five Peirce charges

The columns are the charges `-2, -1, 0, 1, 2`; row `i` records their `i`th
powers. This matrix describes coefficient bookkeeping only. It is not used as
a model of the operator algebra: the operator theorems use the support-based
decomposition and scaled identities over arbitrary rings.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-- The power matrix for the ordered integer charges `(-2,-1,0,1,2)`. -/
def chargePowerMatrix : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => ((j.val : ℤ) - 2) ^ i.val

/-- The five-charge power matrix has determinant `288`. -/
theorem chargePowerMatrix_det : chargePowerMatrix.det = 288 := by
  let v : Fin 5 → ℤ := fun j => (j.val : ℤ) - 2
  have hmatrix : chargePowerMatrix = (Matrix.vandermonde v).transpose := by
    ext i j
    rfl
  rw [hmatrix, Matrix.det_transpose, Matrix.det_vandermonde]
  decide

/-- No integer matrix is a left inverse of the five-charge power matrix. -/
theorem chargePowerMatrix_no_left_inverse (A : Matrix (Fin 5) (Fin 5) ℤ) :
    A * chargePowerMatrix ≠ 1 := by
  intro h
  have hdet : A.det * chargePowerMatrix.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det h
  rw [chargePowerMatrix_det] at hdet
  omega

/-- No integer matrix is a right inverse of the five-charge power matrix. -/
theorem chargePowerMatrix_no_right_inverse (A : Matrix (Fin 5) (Fin 5) ℤ) :
    chargePowerMatrix * A ≠ 1 := by
  intro h
  have hdet : chargePowerMatrix.det * A.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det h
  rw [chargePowerMatrix_det] at hdet
  omega

end InfoGeometry.OperatorAlgebra.PeirceSpine
