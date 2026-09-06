import Mathlib
import proofs.Cl11SheetDiracMatrices

noncomputable section

namespace Cl11CircularBasis

open Cl11SheetDiracMatrices

def a : M2C := (1/2 : ℂ) • (J - K)
def a_dag : M2C := (1/2 : ℂ) • (J + K)

theorem a_sq_zero : a * a = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem a_dag_sq_zero : a_dag * a_dag = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem anticomm_a_a_dag : a * a_dag + a_dag * a = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem a_dag_a_eq_proj_minus : a_dag * a = (1/2 : ℂ) • (1 - Gamma) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem a_a_dag_eq_proj_plus : a * a_dag = (1/2 : ℂ) • (1 + Gamma) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem sheet_sign_eq : a * a_dag - a_dag * a = Gamma := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem reflection_exchange_eq : a + a_dag = J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem phase_axis_eq : a_dag - a = K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

end Cl11CircularBasis
