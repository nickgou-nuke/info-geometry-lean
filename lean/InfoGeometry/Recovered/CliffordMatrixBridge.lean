import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered

/-!
# Cl(1,1) matrix bridge — statement surface

The earlier recovered file attempted to construct the full Clifford algebra lift
using an unproved metric-closure lemma.  This replacement keeps the concrete
linear map and exposes the universal-property obligation as an explicit
proposition.  No algebra homomorphism is installed until that obligation is
proved.
-/

namespace InfoGeometry.Recovered.CliffordMatrixBridge

open Matrix
open InfoGeometry.SplitQuaternion

noncomputable section

/-- The quadratic form with signature `(1,1)` on `Fin 2 → ℚ`. -/
def q11 : QuadraticForm ℚ (Fin 2 → ℚ) := QuadraticMap.proj 0 0 - QuadraticMap.proj 1 1

/-- The concrete function sending the positive generator to `splitJ` and the
negative generator to `splitI`.  Linearity is not packaged here. -/
def cl11ToMatrix (v : Fin 2 → ℚ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (v 0 : ℝ) • splitJ + (v 1 : ℝ) • splitI

/-- Metric-closure obligation needed before constructing a Clifford algebra
homomorphism by the universal property. -/
theorem cl11ToMatrix_sq (v : Fin 2 → ℚ) :
    cl11ToMatrix v * cl11ToMatrix v =
      algebraMap ℚ (Matrix (Fin 2) (Fin 2) ℝ) (q11 v) := by
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cl11ToMatrix, q11, QuadraticMap.proj_apply,
      Algebra.algebraMap_eq_smul_one, splitI, splitJ,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

end

end InfoGeometry.Recovered.CliffordMatrixBridge
