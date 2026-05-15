import Mathlib

/-!
# InfoGeometry.Canonical.FiniteKetMatrixCountBridge

Finite matrix count readbacks.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteKetMatrixCountBridge

/-- Determinant count of a finite square matrix. -/
def determinantCount {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : ℝ :=
  Matrix.det M

/-- The determinant count is the matrix determinant. -/
theorem determinantCount_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : determinantCount M = Matrix.det M := by
  rfl

end InfoGeometry.Canonical.FiniteKetMatrixCountBridge
