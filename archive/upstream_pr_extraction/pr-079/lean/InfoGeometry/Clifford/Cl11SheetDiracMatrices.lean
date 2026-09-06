import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic

namespace InfoGeometry.Clifford

variable {B : Type*} [Ring B]

/-- The identity matrix. -/
def I_mat : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, 1]

/-- The Γ matrix (sheet imbalance / chiral split axis). -/
def Gamma_mat : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, -1]

/-- The J matrix (sheet reflection / exchange). -/
def J_mat : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; 1, 0]

/-- The K = ΓJ matrix (relative phase / internal circular axis). -/
def K_mat : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; -1, 0]

@[simp]
theorem Gamma_sq : Gamma_mat (B := B) * Gamma_mat = I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gamma_mat, I_mat, Matrix.mul_apply]

@[simp]
theorem J_sq : J_mat (B := B) * J_mat = I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mat, I_mat, Matrix.mul_apply]

@[simp]
theorem K_sq : K_mat (B := B) * K_mat = - I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K_mat, I_mat, Matrix.mul_apply]

theorem J_Gamma : J_mat (B := B) * Gamma_mat = - (Gamma_mat * J_mat) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mat, Gamma_mat, Matrix.mul_apply]

theorem K_eq_Gamma_J : K_mat (B := B) = Gamma_mat * J_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K_mat, Gamma_mat, J_mat, Matrix.mul_apply]

end InfoGeometry.Clifford
