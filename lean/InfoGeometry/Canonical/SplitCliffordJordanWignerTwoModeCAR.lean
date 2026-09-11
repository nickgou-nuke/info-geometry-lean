import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option autoImplicit false

/-!
# Genuine two-mode CAR for the existing `M₄(ℝ)` Jordan--Wigner matrices

The matrices are already owned by `SplitCliffordJordanWignerTwoModeCurrent`.
This file adds the missing anticommutation layer by direct finite matrix proof;
it does not identify this carrier with the tensor-tower indexing.
-/

namespace InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCAR

open InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent

theorem a1_square_zero :
    a1 * a1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [a1, Matrix.mul_apply, Fin.sum_univ_four]

theorem a2_square_zero :
    a2 * a2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [a2, Matrix.mul_apply, Fin.sum_univ_four]

theorem a1Dag_square_zero :
    a1Dag * a1Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [a1Dag, Matrix.mul_apply, Fin.sum_univ_four]

theorem a2Dag_square_zero :
    a2Dag * a2Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

theorem a1_a2_anticomm :
    a1 * a2 + a2 * a1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [a1, a2]

theorem a1Dag_a2Dag_anticomm :
    a1Dag * a2Dag + a2Dag * a1Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [a1Dag, a2Dag]

theorem a1Dag_a2_anticomm :
    a1Dag * a2 + a2 * a1Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [a1Dag, a2]

theorem a2Dag_a1_anticomm :
    a2Dag * a1 + a1 * a2Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [a2Dag, a1]

theorem two_mode_CAR_profile :
    a1 * a1 = 0 ∧
    a2 * a2 = 0 ∧
    a1Dag * a1Dag = 0 ∧
    a2Dag * a2Dag = 0 ∧
    a1 * a2 + a2 * a1 = 0 ∧
    a1Dag * a2Dag + a2Dag * a1Dag = 0 ∧
    a1Dag * a2 + a2 * a1Dag = 0 ∧
    a2Dag * a1 + a1 * a2Dag = 0 := by
  exact ⟨a1_square_zero, a2_square_zero, a1Dag_square_zero,
    a2Dag_square_zero, a1_a2_anticomm, a1Dag_a2Dag_anticomm,
    a1Dag_a2_anticomm, a2Dag_a1_anticomm⟩

end InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCAR
