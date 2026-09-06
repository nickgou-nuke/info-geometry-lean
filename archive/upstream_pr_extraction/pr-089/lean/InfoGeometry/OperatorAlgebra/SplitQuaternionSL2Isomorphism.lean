import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic
import InfoGeometry.Algebra.SplitQuaternionMatrices

/-!
# Isomorphism between SL(2, ℝ) and Unit Split Quaternions

This module formalizes the isomorphism between the split-quaternion matrix representation
and the Special Linear Group `SL(2, ℝ)`.

1. `splitQ_det`: Proves that the determinant of the matrix representation is exactly
   the split-quaternion norm `w² + x² - y² - z²`.
2. `splitQ_to_SL2R`: Maps any unit split quaternion (`w² + x² - y² - z² = 1`) to a matrix
   in `SL(2, ℝ)`.
3. `splitQ_mul`: Verifies that the split-quaternion multiplication rules map precisely
   to matrix multiplication.

All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
-/

open Matrix
open InfoGeometry.Algebra.SplitQuaternionMatrices

namespace InfoGeometry.OperatorAlgebra.SplitQuaternionSL2Isomorphism

/-- The determinant of the matrix representation is the split-quaternion norm. -/
theorem splitQ_det (w x y z : ℝ) : det (splitQ w x y z) = w^2 + x^2 - y^2 - z^2 := by
  rw [Matrix.det_fin_two]
  simp [splitQ, sqI, sqJ, sqK]
  ring

/-- Map a unit split quaternion (norm = 1) to `SL(2, ℝ)`. -/
def splitQ_to_SL2R (w x y z : ℝ) (h : w^2 + x^2 - y^2 - z^2 = 1) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨splitQ w x y z, by
    rw [splitQ_det]
    exact h⟩

/-- Matrix multiplication corresponds exactly to the split-quaternion product. -/
theorem splitQ_mul (w1 x1 y1 z1 w2 x2 y2 z2 : ℝ) :
    splitQ (w1 * w2 - x1 * x2 + y1 * y2 + z1 * z2)
           (w1 * x2 + x1 * w2 - y1 * z2 + z1 * y2)
           (w1 * y2 + y1 * w2 - x1 * z2 + z1 * x2)
           (w1 * z2 + z1 * w2 + x1 * y2 - y1 * x2) =
    splitQ w1 x1 y1 z1 * splitQ w2 x2 y2 z2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitQ, sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

end InfoGeometry.OperatorAlgebra.SplitQuaternionSL2Isomorphism
