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

lemma mul_fin_two {α : Type*} [AddCommMonoid α] [Mul α] (A B : Matrix (Fin 2) (Fin 2) α) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  dsimp [Matrix.mul_apply, dotProduct]
  rw [Fin.sum_univ_two]

local macro "mat_simp" : tactic =>
  `(tactic| simp only [P_plus, P_minus, matOneR, matJR, matKR, matOne, matJ, matK, mul_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one, smul_add, mul_add, add_mul, sub_eq_add_neg, neg_mul, mul_neg, neg_zero, sub_zero, zero_sub, neg_neg])

theorem P_plus_add_P_minus : P_plus + P_minus = matOneR := by
  ext i j; fin_cases i <;> fin_cases j
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf

theorem P_plus_sq : P_plus * P_plus = P_plus := by
  ext i j; fin_cases i <;> fin_cases j
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf

theorem P_minus_sq : P_minus * P_minus = P_minus := by
  ext i j; fin_cases i <;> fin_cases j
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf

theorem P_plus_mul_P_minus : P_plus * P_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf

theorem P_minus_mul_P_plus : P_minus * P_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf

theorem matKR_involution : matKR * matKR = matOneR := by
  ext i j; fin_cases i <;> fin_cases j
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf

theorem klein_twist_P_plus : matKR * P_plus * matKR = P_minus := by
  ext i j; fin_cases i <;> fin_cases j
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf

theorem klein_twist_P_minus : matKR * P_minus * matKR = P_plus := by
  ext i j; fin_cases i <;> fin_cases j
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf
  · mat_simp; ring_nf

theorem chiral_reduction (D : RealMat) (h_chiral : D * matJR + matJR * D = 0) :
    D = P_plus * D * P_minus + P_minus * D * P_plus := by
  have h00 : D 0 0 = 0 := by
    have h := congr_arg (fun M => M 0 0) h_chiral
    mat_simp at h
    linarith
  have h11 : D 1 1 = 0 := by
    have h := congr_arg (fun M => M 1 1) h_chiral
    mat_simp at h
    linarith
  
  ext i j; fin_cases i <;> fin_cases j
  · mat_simp
    rw [h00]; ring_nf
  · mat_simp
    ring_nf
  · mat_simp
    ring_nf
  · mat_simp
    rw [h11]; ring_nf

end InfoGeometry.GrandUnification.KleinParabolicPeirceTwist
""")
