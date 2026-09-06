import Mathlib

/-!
# CPT tensor/fractal algebra

Repair of the external tensor file: nilpotency and eigenvector equations are
preserved by Kronecker tensor products.
-/

noncomputable section

namespace CptTensorFractal

open Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Tensor product of two square-zero matrices is square-zero. -/
theorem tensor_nilpotent (A : Matrix n n ℝ) (B : Matrix m m ℝ)
    (hA : A * A = 0) (hB : B * B = 0) :
    Matrix.kronecker A B * Matrix.kronecker A B = 0 := by
  calc
    Matrix.kronecker A B * Matrix.kronecker A B = Matrix.kronecker (A * A) (B * B) := by
      simpa using (Matrix.mul_kronecker_mul A A B B).symm
    _ = 0 := by simp [hA, hB, Matrix.kronecker]

/-- Tensor product of two scale eigenmatrices is again an eigenmatrix. -/
theorem tensor_eigenstate (D_A A : Matrix n n ℝ) (D_B B : Matrix m m ℝ) (lamA lamB : ℝ)
    (hA : D_A * A = lamA • A) (hB : D_B * B = lamB • B) :
    Matrix.kronecker D_A D_B * Matrix.kronecker A B = (lamA * lamB) • Matrix.kronecker A B := by
  calc
    Matrix.kronecker D_A D_B * Matrix.kronecker A B = Matrix.kronecker (D_A * A) (D_B * B) := by
      simpa using (Matrix.mul_kronecker_mul D_A A D_B B).symm
    _ = (lamA * lamB) • Matrix.kronecker A B := by
      rw [hA, hB]
      ext i j
      simp [Matrix.kronecker, Matrix.smul_apply]
      ring

#check tensor_nilpotent
#check tensor_eigenstate

end CptTensorFractal
