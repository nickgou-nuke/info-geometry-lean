import Mathlib

noncomputable section

namespace Cl11SheetDiracMatrices

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Split/chiral axis (Γ) -/
def Gamma : M2C := fun i j =>
  if i = 0 ∧ j = 0 then 1
  else if i = 1 ∧ j = 1 then -1
  else 0

/-- Sheet reflection (J) -/
def J : M2C := fun i j =>
  if i = 0 ∧ j = 1 then 1
  else if i = 1 ∧ j = 0 then 1
  else 0

/-- Circular/phase axis (K = J Γ) -/
def K : M2C := J * Gamma

theorem Gamma_sq : Gamma * Gamma = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gamma, J, K, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem J_sq : J * J = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gamma, J, K, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem anticomm_J_Gamma : J * Gamma = -(Gamma * J) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gamma, J, K, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem K_def : K = J * Gamma := rfl

theorem K_sq : K * K = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gamma, J, K, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

end Cl11SheetDiracMatrices
