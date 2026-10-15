import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Real.Basic

noncomputable section

namespace InfoGeometry.Canonical.SplitCayleyDicksonEquiv

open Matrix

/-!
# Split quaternion algebra equivalence

This module proves an `AlgEquiv ℝ` from Mathlib's quaternion algebra with
parameters `(-1, 0, 1)` to the real 2-by-2 matrix algebra. The equivalence is
an algebraic statement about these carriers; it does not by itself identify a
spin group, a conformal group, or a topological structure.
-/

/-- The split quaternion algebra represented by `QuaternionAlgebra` with
parameters `(-1, 0, 1)`. -/
abbrev SplitQuaternion := QuaternionAlgebra ℝ (-1) 0 1

/-- The explicit algebra map candidate into real 2-by-2 matrices. -/
def splitQuaternionToMatrix (q : SplitQuaternion) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![q.re + q.imJ, q.imI - q.imK],
    ![-q.imI - q.imK, q.re - q.imJ]]

/-- The inverse coordinate map from real 2-by-2 matrices. -/
def matrixToSplitQuaternion (M : Matrix (Fin 2) (Fin 2) ℝ) : SplitQuaternion :=
  let half : ℝ := 1/2
  { re := half * (M 0 0 + M 1 1)
    imI := half * (M 0 1 - M 1 0)
    imJ := half * (M 0 0 - M 1 1)
    imK := half * (-M 0 1 - M 1 0) }

/-- The split quaternion algebra is algebra-isomorphic to `Mat₂(ℝ)`. -/
def splitQuaternionEquivMatrix : SplitQuaternion ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun := splitQuaternionToMatrix
  invFun := matrixToSplitQuaternion
  left_inv q := by
    ext <;> dsimp [splitQuaternionToMatrix, matrixToSplitQuaternion] <;> ring
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [splitQuaternionToMatrix, matrixToSplitQuaternion] <;> ring
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      rw [Matrix.mul_apply] <;>
      simp [splitQuaternionToMatrix, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Fin.sum_univ_two] <;>
      ring
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      rw [Matrix.add_apply] <;>
      simp [splitQuaternionToMatrix, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
      ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitQuaternionToMatrix, Algebra.algebraMap_eq_smul_one]

end InfoGeometry.Canonical.SplitCayleyDicksonEquiv
