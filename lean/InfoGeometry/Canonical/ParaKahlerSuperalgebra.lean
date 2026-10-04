import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix

set_option linter.unusedSimpArgs false

namespace InfoGeometry.ParaKahlerSuperalgebra

variable {R : Type*} [CommRing R]

def a_annihil : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0;
     1, 0]

def a_create : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1;
     0, 0]

def num_op : Matrix (Fin 2) (Fin 2) R :=
  a_create * a_annihil

def chiral_parity : Matrix (Fin 2) (Fin 2) R :=
  a_create * a_annihil - a_annihil * a_create

@[simp] theorem a_annihil_sq :
    (a_annihil : Matrix (Fin 2) (Fin 2) R) * a_annihil = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a_annihil, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem a_create_sq :
    (a_create : Matrix (Fin 2) (Fin 2) R) * a_create = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a_create, Matrix.mul_apply, Fin.sum_univ_succ]

theorem car_relation :
    (a_annihil : Matrix (Fin 2) (Fin 2) R) * a_create + a_create * a_annihil = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [a_annihil, a_create, Matrix.mul_apply, Fin.sum_univ_succ]

theorem num_op_idempotent :
    (num_op : Matrix (Fin 2) (Fin 2) R) * num_op = num_op := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [num_op, a_annihil, a_create, Matrix.mul_apply, Fin.sum_univ_succ]

theorem chiral_parity_sq :
    (chiral_parity : Matrix (Fin 2) (Fin 2) R) * chiral_parity = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_parity, a_annihil, a_create, Matrix.mul_apply, Fin.sum_univ_succ]

theorem chiral_parity_anticomm_create :
    (chiral_parity : Matrix (Fin 2) (Fin 2) R) * a_create + a_create * chiral_parity = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_parity, a_annihil, a_create, Matrix.mul_apply, Fin.sum_univ_succ]

theorem chiral_parity_anticomm_annihil :
    (chiral_parity : Matrix (Fin 2) (Fin 2) R) * a_annihil + a_annihil * chiral_parity = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_parity, a_annihil, a_create, Matrix.mul_apply, Fin.sum_univ_succ]

def J_para : Matrix (Fin 2) (Fin 2) R :=
  chiral_parity

def g_split : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1;
     1, 0]

def omega_form : Matrix (Fin 2) (Fin 2) R :=
  g_split * J_para

theorem paracomplex_sq :
    (J_para : Matrix (Fin 2) (Fin 2) R) * J_para = 1 :=
  chiral_parity_sq

theorem para_hermitian_condition :
    (J_para.transpose : Matrix (Fin 2) (Fin 2) R) * g_split + g_split * J_para = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_para, g_split, chiral_parity, a_annihil, a_create, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]

theorem para_metric_anti_isometry :
    (J_para.transpose : Matrix (Fin 2) (Fin 2) R) * g_split * J_para = - g_split := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_para, g_split, chiral_parity, a_annihil, a_create, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]

theorem omega_skew_symmetric :
    (omega_form.transpose : Matrix (Fin 2) (Fin 2) R) = - omega_form := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [omega_form, J_para, g_split, chiral_parity, a_annihil, a_create, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]

def Q_susy : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

def Q_dag : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0]

def H_susy : Matrix (Fin 4) (Fin 4) R :=
  Q_susy * Q_dag + Q_dag * Q_susy

theorem Q_susy_sq_zero :
    (Q_susy : Matrix (Fin 4) (Fin 4) R) * Q_susy = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Q_susy, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

theorem Q_dag_sq_zero :
    (Q_dag : Matrix (Fin 4) (Fin 4) R) * Q_dag = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Q_dag, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

theorem H_commutes_Q :
    (H_susy : Matrix (Fin 4) (Fin 4) R) * Q_susy - Q_susy * H_susy = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [H_susy, Q_susy, Q_dag, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

theorem H_commutes_Q_dag :
    (H_susy : Matrix (Fin 4) (Fin 4) R) * Q_dag - Q_dag * H_susy = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [H_susy, Q_susy, Q_dag, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

theorem H_susy_diagonal :
    (H_susy : Matrix (Fin 4) (Fin 4) R) =
    !![0, 0, 0, 0;
       0, 1, 0, 0;
       0, 0, 1, 0;
       0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [H_susy, Q_susy, Q_dag, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

end InfoGeometry.ParaKahlerSuperalgebra
