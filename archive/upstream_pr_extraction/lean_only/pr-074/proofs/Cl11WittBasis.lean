import Mathlib
import proofs.Cl11SheetDiracMatrices

noncomputable section

namespace Cl11WittBasis

open Cl11SheetDiracMatrices

def ePlus : M2C := (1/2 : ℂ) • (Gamma + K)
def eMinus : M2C := (1/2 : ℂ) • (Gamma - K)

theorem ePlus_sq_zero : ePlus * ePlus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ePlus, eMinus, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem eMinus_sq_zero : eMinus * eMinus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ePlus, eMinus, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem anticomm_ePlus_eMinus : ePlus * eMinus + eMinus * ePlus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ePlus, eMinus, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem Gamma_eq_ePlus_add_eMinus : Gamma = ePlus + eMinus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ePlus, eMinus, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem K_eq_ePlus_sub_eMinus : K = ePlus - eMinus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ePlus, eMinus, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

end Cl11WittBasis
