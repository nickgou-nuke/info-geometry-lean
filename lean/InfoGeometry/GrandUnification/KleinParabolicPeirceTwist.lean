import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition

namespace InfoGeometry.GrandUnification.KleinParabolicPeirceTwist

open Matrix
open InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition

local notation "RealMat" => Matrix (Fin 2) (Fin 2) ℝ

def matOneR : RealMat := matOne
def matJR : RealMat := matJ
def matKR : RealMat := matK

noncomputable def P_plus : RealMat := (1/2 : ℝ) • (matOneR + matJR)
noncomputable def P_minus : RealMat := (1/2 : ℝ) • (matOneR - matJR)

lemma mat_mul_expand (A B : RealMat) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

macro "mat_eval" : tactic =>
  `(tactic| {
    repeat rw [mat_mul_expand]
    dsimp [P_plus, P_minus, matOneR, matJR, matKR, matOne, matJ, matK]
    try ring
  })

theorem P_plus_add_P_minus : P_plus + P_minus = matOneR := by
  ext i j; fin_cases i <;> fin_cases j <;> mat_eval

theorem P_plus_sq : P_plus * P_plus = P_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> mat_eval

theorem P_minus_sq : P_minus * P_minus = P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> mat_eval

theorem P_plus_mul_P_minus : P_plus * P_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> mat_eval

theorem P_minus_mul_P_plus : P_minus * P_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> mat_eval

theorem matKR_involution : matKR * matKR = matOneR := by
  ext i j; fin_cases i <;> fin_cases j <;> mat_eval

theorem klein_twist_P_plus : matKR * P_plus * matKR = P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> mat_eval

theorem klein_twist_P_minus : matKR * P_minus * matKR = P_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> mat_eval

theorem chiral_reduction (D : RealMat) (h_chiral : D * matJR + matJR * D = 0) :
    D = P_plus * D * P_minus + P_minus * D * P_plus := by
  have h00 : D 0 0 = 0 := by
    have h := congr_arg (fun M => M 0 0) h_chiral
    change (D * matJR) 0 0 + (matJR * D) 0 0 = 0 at h
    repeat rw [mat_mul_expand] at h
    dsimp [matJR, matJ] at h
    linarith
  have h11 : D 1 1 = 0 := by
    have h := congr_arg (fun M => M 1 1) h_chiral
    change (D * matJR) 1 1 + (matJR * D) 1 1 = 0 at h
    repeat rw [mat_mul_expand] at h
    dsimp [matJR, matJ] at h
    linarith
  
  ext i j; fin_cases i <;> fin_cases j
  · change D 0 0 = (P_plus * D * P_minus) 0 0 + (P_minus * D * P_plus) 0 0
    repeat rw [mat_mul_expand]
    dsimp [P_plus, P_minus, matOneR, matJR, matOne, matJ]
    rw [h00]; ring
  · change D 0 1 = (P_plus * D * P_minus) 0 1 + (P_minus * D * P_plus) 0 1
    repeat rw [mat_mul_expand]
    dsimp [P_plus, P_minus, matOneR, matJR, matOne, matJ]
    ring
  · change D 1 0 = (P_plus * D * P_minus) 1 0 + (P_minus * D * P_plus) 1 0
    repeat rw [mat_mul_expand]
    dsimp [P_plus, P_minus, matOneR, matJR, matOne, matJ]
    ring
  · change D 1 1 = (P_plus * D * P_minus) 1 1 + (P_minus * D * P_plus) 1 1
    repeat rw [mat_mul_expand]
    dsimp [P_plus, P_minus, matOneR, matJR, matOne, matJ]
    rw [h11]; ring

-- 5. A finite matrix identity associated with the Klein relation
-- `matKR` normalizes the diagonal matrices by exchanging their entries.
-- This is not a group representation of the Klein bottle: `matA` is
-- parameterized by `ℝ` (including zero), and no map from the presented group
-- is defined here. In the standard SL(2, ℝ) minimal parabolic, this Weyl
-- normalizer representative is outside the parabolic subgroup.
noncomputable def matA (lam : ℝ) : RealMat := (!![lam, 0; 0, lam⁻¹] : Matrix (Fin 2) (Fin 2) ℝ)

/-- Conjugation by the coordinate swap exchanges the entries of this diagonal
matrix. For nonzero `lam`, this is the familiar inversion identity on the
diagonal torus; the statement itself is a matrix identity over all reals. -/
theorem klein_bottle_matrix_relation (lam : ℝ) :
  matKR * matA lam * matKR = matA (lam⁻¹) := by
  ext i j; fin_cases i <;> fin_cases j
  all_goals {
    repeat rw [mat_mul_expand]
    dsimp [matKR, matA, matK]
    try rw [inv_inv]
    try ring
  }

end InfoGeometry.GrandUnification.KleinParabolicPeirceTwist
