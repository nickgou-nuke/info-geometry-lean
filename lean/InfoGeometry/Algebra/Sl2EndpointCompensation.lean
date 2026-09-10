import InfoGeometry.Algebra.FiveGradedLieClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The elementary `sl₂` endpoint relation

This file supplies the smallest concrete realization of the endpoint law used
by the five-grade contract.  It is only the matrix `sl₂` calculation; no
exceptional-algebra identification is asserted.
-/

namespace InfoGeometry.Algebra.Sl2EndpointCompensation

open Matrix

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R

def bracket (A B : Mat2) : Mat2 := A * B - B * A

def ePlus : Mat2 := !![0, 1; 0, 0]

def eMinus : Mat2 := !![0, 0; 1, 0]

def hCartan : Mat2 := !![1, 0; 0, -1]

theorem ePlus_sq : ePlus * ePlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ePlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem eMinus_sq : eMinus * eMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem ePlus_mul_eMinus : ePlus * eMinus = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ePlus, eMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem eMinus_mul_ePlus : eMinus * ePlus = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ePlus, eMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem endpoint_compensation :
    bracket ePlus eMinus = hCartan := by
  rw [bracket, ePlus_mul_eMinus, eMinus_mul_ePlus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hCartan]

/-- Readback in the conventional matrix Lie bracket notation. -/
theorem endpoint_compensation_readback :
    ePlus * eMinus - eMinus * ePlus = hCartan := by
  exact endpoint_compensation

end InfoGeometry.Algebra.Sl2EndpointCompensation
