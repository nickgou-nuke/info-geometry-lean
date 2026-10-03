with open("lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean", "w") as f:
    f.write("""import Mathlib.Data.Real.Basic
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
    try rw [mat_mul_expand]
    try rw [mat_mul_expand]
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
    rw [mat_mul_expand, mat_mul_expand] at h
    dsimp [matJR, matJ] at h
    linarith
  have h11 : D 1 1 = 0 := by
    have h := congr_arg (fun M => M 1 1) h_chiral
    change (D * matJR) 1 1 + (matJR * D) 1 1 = 0 at h
    rw [mat_mul_expand, mat_mul_expand] at h
    dsimp [matJR, matJ] at h
    linarith
  
  ext i j; fin_cases i <;> fin_cases j
  · change D 0 0 = (P_plus * D * P_minus) 0 0 + (P_minus * D * P_plus) 0 0
    rw [mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand]
    dsimp [P_plus, P_minus, matOneR, matJR, matOne, matJ]
    rw [h00]
    ring
  · change D 0 1 = (P_plus * D * P_minus) 0 1 + (P_minus * D * P_plus) 0 1
    rw [mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand]
    dsimp [P_plus, P_minus, matOneR, matJR, matOne, matJ]
    ring
  · change D 1 0 = (P_plus * D * P_minus) 1 0 + (P_minus * D * P_plus) 1 0
    rw [mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand]
    dsimp [P_plus, P_minus, matOneR, matJR, matOne, matJ]
    ring
  · change D 1 1 = (P_plus * D * P_minus) 1 1 + (P_minus * D * P_plus) 1 1
    rw [mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand, mat_mul_expand]
    dsimp [P_plus, P_minus, matOneR, matJR, matOne, matJ]
    rw [h11]
    ring

end InfoGeometry.GrandUnification.KleinParabolicPeirceTwist
""")
