import Mathlib
import proofs.Cl11SheetDiracMatrices
import proofs.Cl11WittBasis
import proofs.Cl11CircularBasis

noncomputable section

namespace CausalDiracMatrixBasisChange

open Cl11SheetDiracMatrices
open Cl11WittBasis
open Cl11CircularBasis

/-- From Witt back to Circular -/
theorem witt_to_circular_a : a = (1/2 : ℂ) • J - (1/2 : ℂ) • (ePlus - eMinus) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, ePlus, eMinus, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem witt_to_circular_a_dag : a_dag = (1/2 : ℂ) • J + (1/2 : ℂ) • (ePlus - eMinus) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, ePlus, eMinus, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

/-- From Circular back to Witt -/
theorem circular_to_witt_ePlus : ePlus = (1/2 : ℂ) • (a * a_dag - a_dag * a) + (1/2 : ℂ) • (a_dag - a) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, ePlus, eMinus, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

theorem circular_to_witt_eMinus : eMinus = (1/2 : ℂ) • (a * a_dag - a_dag * a) - (1/2 : ℂ) • (a_dag - a) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a, a_dag, ePlus, eMinus, Gamma, J, K, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num

/-- From Sheet back to Circular and Witt -/
theorem sheet_Gamma_from_circular : Gamma = a * a_dag - a_dag * a := sheet_sign_eq.symm
theorem sheet_K_from_circular : K = a_dag - a := phase_axis_eq.symm
theorem sheet_J_from_circular : J = a + a_dag := reflection_exchange_eq.symm

theorem sheet_Gamma_from_witt : Gamma = ePlus + eMinus := Gamma_eq_ePlus_add_eMinus
theorem sheet_K_from_witt : K = ePlus - eMinus := K_eq_ePlus_sub_eMinus

end CausalDiracMatrixBasisChange
