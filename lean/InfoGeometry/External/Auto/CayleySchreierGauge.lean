import Mathlib.Tactic

/-!
# Cayley--Schreier gauge finite spin block

The `2×2` Pauli block used for the quaternionic `Q₈` irrep has spinful
time-reversal square `T²=-I`.
-/

noncomputable section

namespace CayleySchreierGauge

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli matrices. -/
def σ1 : M2C := !![0, 1; 1, 0]
def σ2 : M2C := !![0, -I; I, 0]
def σ3 : M2C := !![1, 0; 0, -1]

/-- The two-dimensional quaternion irrep images. -/
def DE_1 : M2C := 1
def DE_i : M2C := -I • σ1
def DE_j : M2C := -I • σ2
def DE_k : M2C := -I • σ3

/-- The spinful time-reversal block. -/
def TE : M2C := I • σ2

/-- `σ₂²=I`. -/
theorem sigma2_sq : σ2 * σ2 = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ2, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- The finite time-reversal block squares to `-I`. -/
theorem emergent_spinful_trs : TE * TE = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [TE, σ2, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- Quaternion irrep generators square to `-I`. -/
theorem quaternion_irrep_squares :
    DE_i * DE_i = -(1 : M2C) ∧ DE_j * DE_j = -(1 : M2C) ∧ DE_k * DE_k = -(1 : M2C) := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [DE_i, σ1, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, Complex.I_mul_I]
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [DE_j, σ2, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, Complex.I_mul_I]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [DE_k, σ3, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, Complex.I_mul_I]

#check sigma2_sq
#check emergent_spinful_trs
#check quaternion_irrep_squares

end CayleySchreierGauge
