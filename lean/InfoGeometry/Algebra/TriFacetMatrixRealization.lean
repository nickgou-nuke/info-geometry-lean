import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
open Matrix

set_option autoImplicit false

namespace Audit.TriFacetMatrixRealization

def O : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem O_sq : O * O = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [O, Matrix.mul_apply]

theorem O_cubed : O * O * O = O := by rw [O_sq, Matrix.one_mul]

noncomputable def P_plus : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 + O)
noncomputable def P_minus : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 - O)
def P_zero : Matrix (Fin 2) (Fin 2) ℂ := 0

theorem O_mul_P_plus : O * P_plus = P_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_plus, O, Matrix.mul_apply]

theorem O_mul_P_minus : O * P_minus = - P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_minus, O, Matrix.mul_apply]

theorem O_mul_P_zero : O * P_zero = 0 := by simp [P_zero]

theorem P_plus_sq : P_plus * P_plus = P_plus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, O, Matrix.mul_apply] <;> field_simp <;> ring

theorem P_minus_sq : P_minus * P_minus = P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_minus, O, Matrix.mul_apply] <;> field_simp <;> ring

theorem P_plus_mul_P_minus : P_plus * P_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, O, Matrix.mul_apply]

theorem P_minus_mul_P_plus : P_minus * P_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, O, Matrix.mul_apply]

theorem P_plus_add_P_minus : P_plus + P_minus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, O] <;> (try field_simp; try ring)

theorem det_O : det (O : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  unfold O; simp [Matrix.det_fin_two]

theorem tr_O : trace (O : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold O; simp

theorem det_P_plus : det (P_plus : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold P_plus; simp [O, Matrix.det_fin_two]

theorem det_P_minus : det (P_minus : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold P_minus; simp [O, Matrix.det_fin_two]

theorem det_krein_J : det (!![(1 : ℂ), 0; 0, (-1 : ℂ)]) = -1 := by
  simp [Matrix.det_fin_two]

end Audit.TriFacetMatrixRealization
