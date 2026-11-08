import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import InfoGeometry.Krein.TomitaMatrixAtom

open Matrix
open InfoGeometry.Krein.TomitaMatrixAtom

set_option linter.unusedSimpArgs false

namespace InfoGeometry.ParaKahlerSuperalgebra

/-! ### 1. The Normalized Chiral Cℓ(1, 1) Ladder Operators -/

/-- Fermionic annihilation operator a ∈ Cℓ(1, 1) ≅ Mat(2, ℝ): a² = 0. -/
def a_annihil : Matrix (Fin 2) (Fin 2) ℝ := ellMinus

/-- Fermionic creation operator a† ∈ Cℓ(1, 1) ≅ Mat(2, ℝ): (a†)² = 0. -/
def a_create : Matrix (Fin 2) (Fin 2) ℝ := ellPlus

/-- Fermionic number operator N = a† * a. -/
def num_op : Matrix (Fin 2) (Fin 2) ℝ := Pplus

/-- Chiral parity grading / Krein involution χ = [a†, a]. -/
def chiral_parity : Matrix (Fin 2) (Fin 2) ℝ := eps

theorem car_relation :
    a_annihil * a_create + a_create * a_annihil = 1 := by
  dsimp [a_annihil, a_create]
  rw [add_comm, ell_anticommutator]

theorem num_op_idempotent :
    num_op * num_op = num_op :=
  Pplus_idempotent

theorem chiral_parity_sq :
    chiral_parity * chiral_parity = 1 :=
  eps_sq

theorem chiral_parity_anticomm_create :
    chiral_parity * a_create + a_create * chiral_parity = 0 := by
  dsimp [chiral_parity, a_create]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [eps, ellPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiral_parity_anticomm_annihil :
    chiral_parity * a_annihil + a_annihil * chiral_parity = 0 := by
  dsimp [chiral_parity, a_annihil]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [eps, ellMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### 2. The Para-Kähler Structure (g, J, Ω) -/

/-- The canonical Paracomplex Structure J = χ = diag(1, -1), satisfying J² = +1. -/
def J_para : Matrix (Fin 2) (Fin 2) ℝ := eps

/-- The split-signature neutral metric g of signature (1, 1). -/
def g_split : Matrix (Fin 2) (Fin 2) ℝ := J

/-- The fundamental 2-form Ω = g * J. -/
def omega_form : Matrix (Fin 2) (Fin 2) ℝ := g_split * J_para

theorem paracomplex_sq :
    J_para * J_para = 1 :=
  eps_sq

theorem para_hermitian_condition :
    J_para.transpose * g_split + g_split * J_para = 0 := by
  dsimp [J_para, g_split]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [eps, J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem para_metric_anti_isometry :
    J_para.transpose * g_split * J_para = - g_split := by
  dsimp [J_para, g_split]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [eps, J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem omega_skew_symmetric :
    omega_form.transpose = - omega_form := by
  dsimp [omega_form, J_para, g_split]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [eps, J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

/-! ### 3. The Chiral Product Superalgebra and SUSY Charges -/

/-- Nilpotent SUSY supercharge Q = a_R† ⊗ a_L in Mat(4, ℝ). -/
def Q_susy : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Conjugate SUSY supercharge Q† = a_R ⊗ a_L† in Mat(4, ℝ). -/
def Q_dag : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0]

/-- Supersymmetric Hamiltonian H = {Q, Q†} = Q * Q† + Q† * Q. -/
def H_susy : Matrix (Fin 4) (Fin 4) ℝ :=
  Q_susy * Q_dag + Q_dag * Q_susy

theorem Q_susy_sq_zero :
    Q_susy * Q_susy = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Q_susy, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

theorem Q_dag_sq_zero :
    Q_dag * Q_dag = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Q_dag, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

theorem H_commutes_Q :
    H_susy * Q_susy - Q_susy * H_susy = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [H_susy, Q_susy, Q_dag, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

theorem H_commutes_Q_dag :
    H_susy * Q_dag - Q_dag * H_susy = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [H_susy, Q_susy, Q_dag, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

theorem H_susy_diagonal :
    H_susy =
    !![0, 0, 0, 0;
       0, 1, 0, 0;
       0, 0, 1, 0;
       0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [H_susy, Q_susy, Q_dag, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_succ]

end InfoGeometry.ParaKahlerSuperalgebra
