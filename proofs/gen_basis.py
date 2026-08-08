import os

def generate_lean():
    lean_code = """import TwoSheetThreeColorWeyl
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option maxHeartbeats 2000000

noncomputable section
namespace SixStateGeneralizedPauliBasis

open TwoSheetThreeColorWeyl
open scoped Matrix

def sheetWeyl (a b : ZMod 2) : M2C := sheetFlip ^ a.val * sheetGamma ^ b.val
def colorWeyl (ω : ℂ) (c d : ZMod 3) : M3C := colorShift ^ c.val * colorClock ω ^ d.val
def sixWeyl (ω : ℂ) (a b : ZMod 2) (c d : ZMod 3) : M6C := tensor (sheetWeyl a b) (colorWeyl ω c d)

theorem tensor_conjTranspose (A : M2C) (B : M3C) : (tensor A B)ᴴ = tensor Aᴴ Bᴴ := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [tensor, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, mul_comm]

theorem sixWeyl_mul (ω : ℂ) (a1 b1 a2 b2 : ZMod 2) (c1 d1 c2 d2 : ZMod 3) :
    sixWeyl ω a1 b1 c1 d1 * sixWeyl ω a2 b2 c2 d2 =
      tensor (sheetWeyl a1 b1 * sheetWeyl a2 b2) (colorWeyl ω c1 d1 * colorWeyl ω c2 d2) := by
  unfold sixWeyl
  exact tensor_mul (sheetWeyl a1 b1) (sheetWeyl a2 b2) (colorWeyl ω c1 d1) (colorWeyl ω c2 d2)

theorem sixWeyl_conjTranspose (ω : ℂ) (a b : ZMod 2) (c d : ZMod 3) :
    (sixWeyl ω a b c d)ᴴ = tensor (sheetWeyl a b)ᴴ (colorWeyl ω c d)ᴴ := by
  unfold sixWeyl
  exact tensor_conjTranspose (sheetWeyl a b) (colorWeyl ω c d)

theorem sixWeyl_trace (ω : ℂ) (a b : ZMod 2) (c d : ZMod 3) :
    Matrix.trace (sixWeyl ω a b c d) = Matrix.trace (sheetWeyl a b) * Matrix.trace (colorWeyl ω c d) := by
  unfold sixWeyl
  exact Matrix.trace_kronecker (sheetWeyl a b) (colorWeyl ω c d)

theorem sheetWeyl_orthogonal (a1 b1 a2 b2 : ZMod 2) (h : (a1, b1) ≠ (a2, b2)) :
    Matrix.trace ((sheetWeyl a1 b1)ᴴ * sheetWeyl a2 b2) = 0 := by
  revert a1 b1 a2 b2 h
  intro a1 b1 a2 b2
  fin_cases a1 <;> fin_cases b1 <;> fin_cases a2 <;> fin_cases b2 <;>
    simp [sheetWeyl, sheetFlip, sheetGamma, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, pow_succ, pow_two] <;>
    intro h <;> (try contradiction) <;> norm_num

theorem colorWeyl_orthogonal (ω : ℂ) (hω : ω^2 + ω + 1 = 0) (c1 d1 c2 d2 : ZMod 3) (h : (c1, d1) ≠ (c2, d2)) :
    Matrix.trace ((colorWeyl ω c1 d1)ᴴ * colorWeyl ω c2 d2) = 0 := by
  revert c1 d1 c2 d2 h
  intro c1 d1 c2 d2
  have hw2 : ω^2 = -ω - 1 := by linear_combination hω
  have hw3 : ω^3 = 1 := by linear_combination (ω - 1) * hω + 1
  have hw4 : ω^4 = ω := by linear_combination (ω^2 - ω) * hω + ω
  fin_cases c1 <;> fin_cases d1 <;> fin_cases c2 <;> fin_cases d2 <;>
    simp [colorWeyl, colorShift, colorClock, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three, pow_succ, pow_two] <;>
    intro h <;> (try contradiction) <;>
    simp [hw2, hw3, hw4] <;> ring

theorem sixWeyl_hilbertSchmidt_orthogonal (ω : ℂ) (hω : ω^2 + ω + 1 = 0) (a1 b1 a2 b2 : ZMod 2) (c1 d1 c2 d2 : ZMod 3)
    (h : (a1, b1, c1, d1) ≠ (a2, b2, c2, d2)) :
    Matrix.trace ((sixWeyl ω a1 b1 c1 d1)ᴴ * sixWeyl ω a2 b2 c2 d2) = 0 := by
  rw [sixWeyl_conjTranspose, sixWeyl_mul, Matrix.trace_kronecker]
  by_cases h1 : (a1, b1) = (a2, b2)
  · have h2 : (c1, d1) ≠ (c2, d2) := by
      intro hc
      apply h
      ext
      · exact congr_arg Prod.fst h1
      · exact congr_arg Prod.snd h1
      · exact congr_arg Prod.fst hc
      · exact congr_arg Prod.snd hc
    rw [colorWeyl_orthogonal ω hω _ _ _ _ h2, mul_zero]
  · rw [sheetWeyl_orthogonal _ _ _ _ h1, zero_mul]

theorem sixWeyl_trace_self (ω : ℂ) (a b : ZMod 2) (c d : ZMod 3) :
    Matrix.trace ((sixWeyl ω a b c d)ᴴ * sixWeyl ω a b c d) = 6 := by
  revert a b c d
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [sixWeyl, sheetWeyl, colorWeyl, colorShift, colorClock, sheetFlip, sheetGamma, tensor, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, Matrix.kroneckerMap_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, pow_succ, pow_two] <;>
    norm_num

theorem sixWeyl_linearIndependent (ω : ℂ) (hω : ω^2 + ω + 1 = 0) :
    LinearIndependent ℂ (fun (p : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3) =>
      sixWeyl ω p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f hf
  ext ⟨a1, ⟨b1, ⟨c1, d1⟩⟩⟩
  have h1 : Matrix.trace ((sixWeyl ω a1 b1 c1 d1)ᴴ * (∑ q : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3, f q • sixWeyl ω q.1 q.2.1 q.2.2.1 q.2.2.2)) =
    Matrix.trace ((sixWeyl ω a1 b1 c1 d1)ᴴ * 0) := by rw [hf]
  rw [Matrix.mul_zero, Matrix.trace_zero] at h1
  rw [Finset.mul_sum] at h1
  simp_rw [Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul] at h1
  have h2 : (∑ q : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3, f q * Matrix.trace ((sixWeyl ω a1 b1 c1 d1)ᴴ * sixWeyl ω q.1 q.2.1 q.2.2.1 q.2.2.2)) = f (a1, b1, c1, d1) * 6 := by
    rw [Finset.sum_eq_single (a1, b1, c1, d1)]
    · intro q _ hq
      rcases q with ⟨a2, ⟨b2, ⟨c2, d2⟩⟩⟩
      have hq' : (a1, b1, c1, d1) ≠ (a2, b2, c2, d2) := by
        intro hc
        apply hq
        ext
        · exact congr_arg (fun x => x.1) hc
        · exact congr_arg (fun x => x.2.1) hc
        · exact congr_arg (fun x => x.2.2.1) hc
        · exact congr_arg (fun x => x.2.2.2) hc
      rw [sixWeyl_hilbertSchmidt_orthogonal ω hω a1 b1 a2 b2 c1 d1 c2 d2 hq', mul_zero]
    · intro hq
      exfalso
      apply hq
      exact Finset.mem_univ _
    · rw [sixWeyl_trace_self]
  rw [h2] at h1
  exact (mul_eq_zero.mp h1).resolve_right (by norm_num)

noncomputable def sixWeyl_basis (ω : ℂ) (hω : ω^2 + ω + 1 = 0) : Basis (ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3) ℂ M6C :=
  basisOfLinearIndependentOfCardEqFinrank (sixWeyl_linearIndependent ω hω) (by simp [Module.finrank_matrix])

end SixStateGeneralizedPauliBasis
end noncomputable section
"""
    with open('/home/goutev/auto/proofs/SixStateGeneralizedPauliBasis.lean', 'w') as f:
        f.write(lean_code)

if __name__ == '__main__':
    generate_lean()
