import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic

noncomputable section

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] [Fintype σ]

/-- 
Key Lemma: If variable i has degree ≤ 1 in P, then P is a linear function of i.
-/
theorem multiaffine_linearity (i : σ) (P : MvPolynomial σ ℂ)
    (hdeg : degreeOf i P ≤ 1) (z : σ → ℂ) :
    ∃ a b, ∀ x, eval (Function.update z i x) P = a + b * x := by
  let S := P.support
  have h_mi : ∀ m ∈ S, m i ≤ 1 := degreeOf_le_iff.mp hdeg
  
  let f_m (m : σ →₀ ℕ) : ℂ := (coeff m P) * ∏ j ∈ Finset.univ.erase i, (z j)^(m j)
  
  let a := ∑ m ∈ S, (if m i = 0 then f_m m else 0)
  let b := ∑ m ∈ S, (if m i = 1 then f_m m else 0)
  
  use a, b
  intro x
  rw [as_sum P, eval_sum]
  simp only [eval_monomial, Function.update_apply]
  
  trans ∑ m ∈ S, (if m i = 0 then f_m m else f_m m * x)
  · apply Finset.sum_congr rfl
    intro m hm
    have := h_mi m hm
    rw [Finsupp.prod_eq_prod_univ]
    rw [← Finset.insert_erase (Finset.mem_univ i)]
    rw [Finset.prod_insert (Finset.not_mem_erase i _)]
    simp only [Function.update_apply, if_pos rfl]
    unfold f_m
    split_ifs with h0 h1
    · simp [h0]; ring
    · simp [h1]; ring
    · omega
  · simp [Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have := h_mi m hm
    split_ifs with h0 h1
    · simp [h0]
    · simp [h1]; ring
    · omega
