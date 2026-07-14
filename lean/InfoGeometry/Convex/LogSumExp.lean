import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

/-!
# Finite Log-Sum-Exp Gauge

Finite-coordinate scalar gauge facts for logits: positivity of the exponential
partition sum, translation of log-sum-exp under uniform shifts, invariance of
softmax under that shift, and normalization.
-/

namespace InfoGeometry.Convex.LogSumExp

variable {n : Type*} [Fintype n] [Nonempty n]

/-- Finite real logits indexed by `n`. -/
abbrev RN := n → ℝ

/-- Uniform logit-shift direction. -/
def uniformShift : RN (n := n) := fun _ => 1

/-- Exponential partition sum `∑ᵢ exp(xᵢ)`. -/
noncomputable def sumExp (x : RN (n := n)) : ℝ :=
  ∑ i, Real.exp (x i)

/-- Log-sum-exp potential. -/
noncomputable def lse (x : RN (n := n)) : ℝ :=
  Real.log (sumExp x)

/-- Softmax weights. -/
noncomputable def softmax (x : RN (n := n)) : RN (n := n) :=
  fun i => Real.exp (x i) / sumExp x

lemma sumExp_pos (x : RN (n := n)) :
    0 < sumExp x := by
  unfold sumExp
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset n))
      (f := fun i => Real.exp (x i))
      (by
        intro i hi
        exact Real.exp_pos _)
      Finset.univ_nonempty)

omit [Nonempty n] in
lemma sumExp_add_const (x : RN (n := n)) (c : ℝ) :
    sumExp (x + c • uniformShift) = Real.exp c * sumExp x := by
  unfold sumExp uniformShift
  calc
    ∑ i, Real.exp ((x + c • fun _ : n => (1 : ℝ)) i)
        = ∑ i, Real.exp (x i) * Real.exp c := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [Pi.add_apply, Pi.smul_apply, Real.exp_add]
    _ = (∑ i, Real.exp (x i)) * Real.exp c := by
          rw [Finset.sum_mul]
    _ = Real.exp c * ∑ i, Real.exp (x i) := by
          rw [mul_comm]

theorem lse_add_uniformShift (x : RN (n := n)) (c : ℝ) :
    lse (x + c • uniformShift) = lse x + c := by
  unfold lse
  rw [sumExp_add_const]
  have hsum : 0 < sumExp x := sumExp_pos x
  have hexp : 0 < Real.exp c := Real.exp_pos c
  rw [Real.log_mul hexp.ne' hsum.ne', Real.log_exp, add_comm]

theorem softmax_add_uniformShift (x : RN (n := n)) (c : ℝ) :
    softmax (x + c • uniformShift) = softmax x := by
  ext i
  unfold softmax
  rw [sumExp_add_const]
  have hshift : (x + c • uniformShift (n := n)) i = x i + c := by
    simp [uniformShift]
  rw [hshift, Real.exp_add]
  have hne : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  have hsum_ne : sumExp x ≠ 0 := (sumExp_pos x).ne'
  field_simp [hne, hsum_ne]

theorem sum_softmax_eq_one (x : RN (n := n)) :
    ∑ i, softmax x i = 1 := by
  unfold softmax
  calc
    ∑ i, Real.exp (x i) / sumExp x
        = (∑ i, Real.exp (x i)) / sumExp x := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset n))
                (f := fun i => Real.exp (x i))
                (a := sumExp x))
    _ = 1 := by
          rw [show (∑ i, Real.exp (x i)) = sumExp x by rfl]
          exact div_self (sumExp_pos x).ne'

lemma softmax_nonneg (x : RN (n := n)) (i : n) :
    0 ≤ softmax x i := by
  unfold softmax
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (sumExp_pos x))

lemma softmax_le_one (x : RN (n := n)) (i : n) :
    softmax x i ≤ 1 := by
  have hnonneg : ∀ j : n, 0 ≤ softmax x j := fun j => softmax_nonneg x j
  have hsum : ∑ j : n, softmax x j = 1 := sum_softmax_eq_one x
  have hi_le_sum : softmax x i ≤ ∑ j : n, softmax x j := by
    exact Finset.single_le_sum (fun j _hj => hnonneg j) (Finset.mem_univ i)
  simpa [hsum] using hi_le_sum

end InfoGeometry.Convex.LogSumExp
