import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Square-zero operators and their cross terms

Square-zero equations for two operators do not imply square-zero for their
sum. This owner records the exact `2 × 2` matrix-unit example: each off-diagonal
matrix unit squares to zero, while their sum squares to the identity. It is an
algebraic counterexample only; it makes no amplituhedron or supersymmetry claim.
-/

namespace InfoGeometry.Canonical.NativeMathlibSuperamplituhedronBridge

open Matrix

/-- The upper off-diagonal matrix unit in dimension two. -/
def upperUnit : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- The lower off-diagonal matrix unit in dimension two. -/
def lowerUnit : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- The upper matrix unit is a nonzero square-zero operator. -/
theorem upperUnit_sq_zero : upperUnit * upperUnit = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperUnit, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower matrix unit is a nonzero square-zero operator. -/
theorem lowerUnit_sq_zero : lowerUnit * lowerUnit = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerUnit, Matrix.mul_apply, Fin.sum_univ_two]

/-- Their sum is not square-zero: it squares to the identity matrix. -/
theorem sum_matrixUnits_sq_eq_one :
    (upperUnit + lowerUnit) * (upperUnit + lowerUnit) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperUnit, lowerUnit, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two cross-products add to the identity; this is exactly the term that
prevents the sum of these square-zero operators from being square-zero. -/
theorem matrixUnits_cross_terms_eq_one :
    upperUnit * lowerUnit + lowerUnit * upperUnit = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperUnit, lowerUnit, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.NativeMathlibSuperamplituhedronBridge
