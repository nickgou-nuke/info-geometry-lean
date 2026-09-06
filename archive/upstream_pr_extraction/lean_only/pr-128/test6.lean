import Mathlib

def Gamma_matrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem Gamma_sq : Gamma_matrix * Gamma_matrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [Gamma_matrix, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
