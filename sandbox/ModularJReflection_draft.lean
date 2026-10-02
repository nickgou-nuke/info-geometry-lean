import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

variable {R : Type*} [CommRing R]

def J_CP : Matrix (Fin 2) (Fin 2) R :=
  ![![1, 0],
    ![0, -1]]

lemma J_CP_sq : J_CP * J_CP = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def deriv_matrix (X dX : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![X, dX],
    ![0, X]]

lemma cp_sign_flip (X dX : R) :
  J_CP * deriv_matrix X dX * J_CP = deriv_matrix X (-dX) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [J_CP, deriv_matrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
  ring
