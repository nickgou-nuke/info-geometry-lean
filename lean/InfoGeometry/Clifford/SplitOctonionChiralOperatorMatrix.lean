import InfoGeometry.Clifford.QuaternionPauliRealForm
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Chiral operator matrices with quaternionic Pauli entries

The outer `2 × 2` matrices are ordinary operators whose entries are the
already verified quaternionic Pauli matrices.  This gives an eight-generator
chiral carrier without Zorn vector slots.  It is a linear/associative ambient
space; the non-associative split-octonion product is not identified with its
ordinary block multiplication.
-/

namespace InfoGeometry.Clifford.SplitOctonionChiralOperatorMatrix

open InfoGeometry.Clifford.QuaternionPauliRealForm
open scoped Matrix

abbrev BlockMat := Matrix (Fin 2) (Fin 2) Mat2C

def blockZero : Mat2C := 0

def blockOne : Mat2C := 1

def L : BlockMat := !![blockOne, blockZero; blockZero, -blockOne]

def R : BlockMat := !![blockZero, blockOne; blockOne, blockZero]

noncomputable def J : BlockMat := L * R

def UPlus : BlockMat := !![blockOne, blockZero; blockZero, blockZero]

def UMinus : BlockMat := !![blockZero, blockZero; blockZero, blockOne]

def E1 : BlockMat := !![blockZero, qi; qi, blockZero]

def E2 : BlockMat := !![blockZero, qj; qj, blockZero]

def E3 : BlockMat := !![blockZero, qk; qk, blockZero]

noncomputable def E1Plus : BlockMat := UPlus * E1

noncomputable def E1Minus : BlockMat := UMinus * E1

noncomputable def E2Plus : BlockMat := UPlus * E2

noncomputable def E2Minus : BlockMat := UMinus * E2

noncomputable def E3Plus : BlockMat := UPlus * E3

noncomputable def E3Minus : BlockMat := UMinus * E3

noncomputable def EPlus : Fin 3 → BlockMat
  | 0 => E1Plus
  | 1 => E2Plus
  | 2 => E3Plus

noncomputable def EMinus : Fin 3 → BlockMat
  | 0 => E1Minus
  | 1 => E2Minus
  | 2 => E3Minus

/-- The undivided quaternionic block family. -/
def E : Fin 3 → BlockMat
  | 0 => E1
  | 1 => E2
  | 2 => E3

@[simp] theorem L_sq : L * L = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [L, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem R_sq : R * R = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem R_conjugate_swap_blocks (X : BlockMat) :
    R * X * R = !![X 1 1, X 1 0; X 0 1, X 0 0] := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, blockOne, blockZero, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]

theorem R_conjugate_involutive (X : BlockMat) :
    R * (R * X * R) * R = X := by
  calc
    R * (R * X * R) * R = (R * R) * X * (R * R) := by
      noncomm_ring
    _ = X := by rw [R_sq]; simp

theorem R_L_R : R * L * R = -L := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, L, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem R_conjugate_smul_L (κ : ℝ) :
    R * (κ • L) * R = -(κ • L) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, L, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem L_R_anticomm : L * R + R * L = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, L, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem J_sq : J * J = -(1 : BlockMat) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [J, R, L, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem R_L_anticomm : R * L + L * R = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, L, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem J_R_anticomm : J * R + R * J = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [J, R, L, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem L_UPlus_diff : UPlus - UMinus = L := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [UPlus, UMinus, L, blockOne, blockZero]

theorem E1_sq : E1 * E1 = -(1 : BlockMat) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E1, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two,
      qi_sq]

theorem E2_sq : E2 * E2 = -(1 : BlockMat) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E2, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two,
      qj_sq]

theorem E3_sq : E3 * E3 = -(1 : BlockMat) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E3, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two,
      qk_sq]

theorem L_E1_anticomm : L * E1 + E1 * L = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [L, E1, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem L_E2_anticomm : L * E2 + E2 * L = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [L, E2, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem L_E3_anticomm : L * E3 + E3 * L = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [L, E3, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem E1_chiral_split : E1Plus + E1Minus = E1 := by
    simp [E1Plus, E1Minus, E1, UPlus, UMinus, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem R_UPlus_R : R * UPlus * R = UMinus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, UPlus, UMinus, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem R_E1Plus_R : R * E1Plus * R = E1Minus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, E1Plus, E1Minus, UPlus, UMinus, E1, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem R_E2Plus_R : R * E2Plus * R = E2Minus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, E2Plus, E2Minus, UPlus, UMinus, E2, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem R_E3Plus_R : R * E3Plus * R = E3Minus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, E3Plus, E3Minus, UPlus, UMinus, E3, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem R_UMinus_R : R * UMinus * R = UPlus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, UPlus, UMinus, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem R_E1Minus_R : R * E1Minus * R = E1Plus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, E1Plus, E1Minus, UPlus, UMinus, E1, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem R_E2Minus_R : R * E2Minus * R = E2Plus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, E2Plus, E2Minus, UPlus, UMinus, E2, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem R_E3Minus_R : R * E3Minus * R = E3Plus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [R, E3Plus, E3Minus, UPlus, UMinus, E3, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem E2_chiral_split : E2Plus + E2Minus = E2 := by
  simp [E2Plus, E2Minus, E2, UPlus, UMinus, blockOne, blockZero,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem E3_chiral_split : E3Plus + E3Minus = E3 := by
  simp [E3Plus, E3Minus, E3, UPlus, UMinus, blockOne, blockZero,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem E1Plus_sq : E1Plus * E1Plus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E1Plus, UPlus, E1, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem E2Plus_sq : E2Plus * E2Plus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E2Plus, UPlus, E2, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem E3Plus_sq : E3Plus * E3Plus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
      simp [E3Plus, UPlus, E3, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem EPlus_mul_EPlus_zero (a b : Fin 3) :
    EPlus a * EPlus b = 0 := by
  fin_cases a <;> fin_cases b <;>
    ext r c <;>
    fin_cases r <;> fin_cases c <;>
    simp [EPlus, E1Plus, E2Plus, E3Plus, UPlus, E1, E2, E3,
      blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem UPlus_sq : UPlus * UPlus = UPlus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [UPlus, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem UMinus_sq : UMinus * UMinus = UMinus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [UMinus, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem UPlus_UMinus_zero : UPlus * UMinus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [UPlus, UMinus, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem UMinus_UPlus_zero : UMinus * UPlus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [UPlus, UMinus, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem E1Plus_E2Plus_zero : E1Plus * E2Plus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E1Plus, E2Plus, UPlus, E1, E2, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem E2Plus_E3Plus_zero : E2Plus * E3Plus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E2Plus, E3Plus, UPlus, E2, E3, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem E3Plus_E1Plus_zero : E3Plus * E1Plus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E3Plus, E1Plus, UPlus, E3, E1, blockOne, blockZero,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem E1Minus_sq : E1Minus * E1Minus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E1Minus, UMinus, E1, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem E2Minus_sq : E2Minus * E2Minus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E2Minus, UMinus, E2, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem E3Minus_sq : E3Minus * E3Minus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [E3Minus, UMinus, E3, blockOne, blockZero, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem EMinus_mul_EMinus_zero (a b : Fin 3) :
    EMinus a * EMinus b = 0 := by
  fin_cases a <;> fin_cases b <;>
    ext r c <;>
    fin_cases r <;> fin_cases c <;>
    simp [EMinus, E1Minus, E2Minus, E3Minus, UMinus, E1, E2, E3,
      blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

/-! The mixed chiral products generate the diagonal quaternion sector. -/

noncomputable def D1 : BlockMat := E1 * R

noncomputable def D2 : BlockMat := E2 * R

noncomputable def D3 : BlockMat := E3 * R

/-- Indexed form of the diagonal quaternionic envelope generators. -/
noncomputable def diagD : Fin 3 → BlockMat
  | 0 => D1
  | 1 => D2
  | 2 => D3

theorem diagD_zero : diagD 0 = D1 := rfl

theorem diagD_one : diagD 1 = D2 := rfl

theorem diagD_two : diagD 2 = D3 := rfl

theorem diagonal_quaternion_packet :
    D1 * D1 = -(1 : BlockMat) ∧
    D2 * D2 = -(1 : BlockMat) ∧
    D3 * D3 = -(1 : BlockMat) ∧
    D1 * D2 = D3 ∧
    D2 * D3 = D1 ∧
    D3 * D1 = D2 := by
  repeat' constructor
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [D1, E1, R, blockOne, blockZero, Matrix.mul_apply,
        Fin.sum_univ_two, qi_sq]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [D2, E2, R, blockOne, blockZero, Matrix.mul_apply,
        Fin.sum_univ_two, qj_sq]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [D3, E3, R, blockOne, blockZero, Matrix.mul_apply,
        Fin.sum_univ_two, qk_sq]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [D1, D2, D3, E1, E2, E3, R, blockOne, blockZero,
        Matrix.mul_apply, Fin.sum_univ_two, qi_mul_qj]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [D1, D2, D3, E1, E2, E3, R, blockOne, blockZero,
        Matrix.mul_apply, Fin.sum_univ_two, qj_mul_qk]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [D1, D2, D3, E1, E2, E3, R, blockOne, blockZero,
        Matrix.mul_apply, Fin.sum_univ_two, qi_mul_qj, qj_mul_qk,
        qk_mul_qi]

theorem mixed_chiral_product_packet :
    E1Plus * E1Minus = -UPlus ∧
    E2Plus * E2Minus = -UPlus ∧
    E3Plus * E3Minus = -UPlus ∧
    E1Minus * E1Plus = -UMinus ∧
    E2Minus * E2Plus = -UMinus ∧
    E3Minus * E3Plus = -UMinus := by
  constructor
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [E1Plus, E1Minus, UPlus, UMinus, E1, blockOne, blockZero,
        Matrix.mul_apply, Fin.sum_univ_two, qi_sq]
  constructor
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [E2Plus, E2Minus, UPlus, UMinus, E2, blockOne, blockZero,
        Matrix.mul_apply, Fin.sum_univ_two, qj_sq]
  constructor
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [E3Plus, E3Minus, UPlus, UMinus, E3, blockOne, blockZero,
        Matrix.mul_apply, Fin.sum_univ_two, qk_sq]
  constructor
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [E1Plus, E1Minus, UPlus, UMinus, E1, blockOne, blockZero,
        Matrix.mul_apply, Fin.sum_univ_two, qi_sq]
  constructor
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [E2Plus, E2Minus, UPlus, UMinus, E2, blockOne, blockZero,
        Matrix.mul_apply, Fin.sum_univ_two, qj_sq]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [E3Plus, E3Minus, UPlus, UMinus, E3, blockOne, blockZero,
        Matrix.mul_apply, Fin.sum_univ_two, qk_sq]

theorem mixed_chiral_commutator_same_index :
    (E1Plus * E1Minus - E1Minus * E1Plus = -L) ∧
    (E2Plus * E2Minus - E2Minus * E2Plus = -L) ∧
    (E3Plus * E3Minus - E3Minus * E3Plus = -L) := by
  rcases mixed_chiral_product_packet with ⟨h1, h2, h3, h4, h5, h6⟩
  constructor
  · rw [h1, h4]
    calc
      -UPlus - -UMinus = -(UPlus - UMinus) := by noncomm_ring
      _ = -L := by rw [L_UPlus_diff]
  constructor
  · rw [h2, h5]
    calc
      -UPlus - -UMinus = -(UPlus - UMinus) := by noncomm_ring
      _ = -L := by rw [L_UPlus_diff]
  · rw [h3, h6]
    calc
      -UPlus - -UMinus = -(UPlus - UMinus) := by noncomm_ring
      _ = -L := by rw [L_UPlus_diff]

/-! The indexed mixed laws retain the full diagonal quaternion sector. -/

theorem EPlus_mul_EMinus_indexed (a b : Fin 3) :
    EPlus a * EMinus b = UPlus * (diagD a * diagD b) := by
  fin_cases a <;> fin_cases b <;>
    ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [EPlus, EMinus, diagD, D1, D2, D3, E1Plus, E1Minus,
      E2Plus, E2Minus, E3Plus, E3Minus, UPlus, UMinus, E1, E2, E3,
      R, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem EMinus_mul_EPlus_indexed (a b : Fin 3) :
    EMinus a * EPlus b = UMinus * (diagD a * diagD b) := by
  fin_cases a <;> fin_cases b <;>
    ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [EPlus, EMinus, diagD, D1, D2, D3, E1Plus, E1Minus,
      E2Plus, E2Minus, E3Plus, E3Minus, UPlus, UMinus, E1, E2, E3,
      R, blockOne, blockZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem mixed_commutator_indexed (a b : Fin 3) :
    EPlus a * EMinus b - EMinus b * EPlus a =
      UPlus * (diagD a * diagD b) - UMinus * (diagD b * diagD a) := by
  rw [EPlus_mul_EMinus_indexed, EMinus_mul_EPlus_indexed]

theorem mixed_anticommutator_indexed (a b : Fin 3) :
    EPlus a * EMinus b + EMinus b * EPlus a =
      UPlus * (diagD a * diagD b) + UMinus * (diagD b * diagD a) := by
  rw [EPlus_mul_EMinus_indexed, EMinus_mul_EPlus_indexed]

end InfoGeometry.Clifford.SplitOctonionChiralOperatorMatrix
