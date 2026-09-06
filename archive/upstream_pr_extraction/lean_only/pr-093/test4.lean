import Mathlib

open Matrix
open scoped Matrix ComplexOrder

namespace InfoGeometry.OperatorAlgebraicLorentzLift

set_option linter.unusedSectionVars false

def Gamma_matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

def J_matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

theorem Gamma_sq : Gamma_matrix ^ 2 = 1 := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;> 
  · dsimp [Gamma_matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.head_cons, Matrix.empty_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem J_sq : J_matrix ^ 2 = 1 := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;> 
  · dsimp [J_matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.head_cons, Matrix.empty_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem Gamma_J_anti_comm : Gamma_matrix * J_matrix + J_matrix * Gamma_matrix = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> 
  · dsimp [Gamma_matrix, J_matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.head_cons, Matrix.empty_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

end InfoGeometry.OperatorAlgebraicLorentzLift
