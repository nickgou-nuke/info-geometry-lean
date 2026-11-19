/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.UnitInterval
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli
import InfoGeometry.Arithmetic.GenuineBounds

namespace InfoGeometry.Arithmetic.ChebyshevPrimeAndHoeffdingBounds

open scoped BigOperators
open MeasureTheory ProbabilityTheory unitInterval

/-! ## Part 1 — Hoeffding Bernoulli MGF & Binomial Tail Bounds -/

/-- Hoeffding's lemma for Bernoulli random variables:
The moment generating function satisfies $\mathbb{E}[e^{t(X - p)}] \le e^{t^2 / 8}$. -/
theorem hoeffding_bernoulli_mgf (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-t * p) ≤ Real.exp (t ^ 2 / 8) := by
  let p_I : I := ⟨p, hp0, hp1⟩
  let μ := bernoulliMeasure (1 - p) (-p) p_I
  have hm : AEMeasurable id μ := measurable_id.aemeasurable
  have hb : ∀ᵐ ω ∂μ, id ω ∈ Set.Icc (-p) (1 - p) := by
    rw [ae_iff]
    have hsub : {ω : ℝ | id ω ∉ Set.Icc (-p) (1 - p)} ⊆ {1 - p, -p}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      intro h_cases
      rcases h_cases with rfl | rfl
      · apply hx
        simp only [id_eq, Set.mem_Icc]
        exact ⟨by linarith, by linarith⟩
      · apply hx
        simp only [id_eq, Set.mem_Icc]
        exact ⟨by linarith, by linarith⟩
    refine measure_mono_null hsub ?_
    rw [bernoulliMeasure_apply_of_notMem_of_notMem p_I]
    · exact ((measurableSet_singleton (-p)).insert (1 - p)).compl
    · simp
    · simp
  have hc : μ[id] = 0 := by
    change ∫ z, z ∂(bernoulliMeasure (1 - p) (-p) p_I) = 0
    have hint := integral_bernoulliMeasure (1 - p) (-p) p_I id
    simp only [id_eq, smul_eq_mul] at hint
    rw [hint]
    have : (p_I : ℝ) = p := rfl
    rw [this]
    ring
  have h_subg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc
  have h_mgf := h_subg.mgf_le t
  have hdiff : (1 - p : ℝ) - -p = 1 := by ring
  have h_norm : ‖(1 - p : ℝ) - -p‖₊ = 1 := by
    rw [hdiff, nnnorm_one]
  have h_c_coe : (((‖(1 - p : ℝ) - -p‖₊ / 2) ^ 2 : NNReal) : ℝ) = 1 / 4 := by
    rw [h_norm]
    push_cast
    ring
  have h_exp_eq : (((‖(1 - p : ℝ) - -p‖₊ / 2) ^ 2 : NNReal) : ℝ) * t ^ 2 / 2 = t ^ 2 / 8 := by
    rw [h_c_coe]
    ring
  have h_mgf_eq : mgf id μ t =
      p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-t * p) := by
    change ∫ z, Real.exp (t * z) ∂(bernoulliMeasure (1 - p) (-p) p_I) =
      p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-t * p)
    have hint := integral_bernoulliMeasure (1 - p) (-p) p_I
      (fun z => Real.exp (t * id z))
    simp only [id_eq, smul_eq_mul] at hint
    rw [hint]
    have : (p_I : ℝ) = p := rfl
    rw [this]
    ring_nf
  rw [h_mgf_eq] at h_mgf
  rw [h_exp_eq] at h_mgf
  exact h_mgf

/-- Two-sided binomial tail probability $|k/Q - p| \ge \varepsilon$. -/
noncomputable def binomTailProb (Q : ℕ) (p ε : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (Q + 1)).filter (fun (k : ℕ) => |(k : ℝ) / (Q : ℝ) - p| ≥ ε),
    (Nat.choose Q k : ℝ) * p ^ k * (1 - p) ^ (Q - k)

/-- At $\varepsilon = 0$, the tail probability equals 1 by the binomial theorem. -/
theorem binomTailProb_zero (Q : ℕ) (p : ℝ) :
    binomTailProb Q p 0 = 1 := by
  have hfilter : (Finset.range (Q + 1)).filter (fun (k : ℕ) => |(k : ℝ) / (Q : ℝ) - p| ≥ 0) =
      Finset.range (Q + 1) := by
    ext k
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro _
    exact abs_nonneg _
  unfold binomTailProb
  rw [hfilter]
  have h_binom : ∑ k ∈ Finset.range (Q + 1), p ^ k * (1 - p) ^ (Q - k) * (Nat.choose Q k : ℝ) =
      (p + (1 - p)) ^ Q := (add_pow p (1 - p) Q).symm
  have h_add : p + (1 - p) = 1 := by ring
  rw [h_add, one_pow] at h_binom
  have h_terms : (∑ k ∈ Finset.range (Q + 1), (Nat.choose Q k : ℝ) * p ^ k * (1 - p) ^ (Q - k)) =
      ∑ k ∈ Finset.range (Q + 1), p ^ k * (1 - p) ^ (Q - k) * (Nat.choose Q k : ℝ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h_terms, h_binom]

lemma binom_weighted_sum_upper (Q : ℕ) (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ k ∈ Finset.range (Q + 1), (Nat.choose Q k : ℝ) * p ^ k * (1 - p) ^ (Q - k) *
      Real.exp (t * ((k : ℝ) - (Q : ℝ) * p)) ≤ Real.exp ((Q : ℝ) * (t ^ 2 / 8)) := by
  have h_exp_term : ∀ k : ℕ, Real.exp (t * ((k : ℝ) - (Q : ℝ) * p)) =
      (Real.exp (-t * p)) ^ Q * (Real.exp t) ^ k := by
    intro k
    have h1 : t * ((k : ℝ) - (Q : ℝ) * p) = (k : ℝ) * t + (Q : ℝ) * (-t * p) := by ring
    rw [h1, Real.exp_add]
    have hk : Real.exp ((k : ℝ) * t) = (Real.exp t) ^ k := Real.exp_nat_mul t k
    have hQ : Real.exp ((Q : ℝ) * (-t * p)) = (Real.exp (-t * p)) ^ Q := Real.exp_nat_mul (-t * p) Q
    rw [hk, hQ, mul_comm]
  have h_terms : (∑ k ∈ Finset.range (Q + 1), (Nat.choose Q k : ℝ) * p ^ k * (1 - p) ^ (Q - k) *
      Real.exp (t * ((k : ℝ) - (Q : ℝ) * p))) =
      (Real.exp (-t * p)) ^ Q * ∑ k ∈ Finset.range (Q + 1), (p * Real.exp t) ^ k * (1 - p) ^ (Q - k) *
        (Nat.choose Q k : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h_exp_term k]
    ring
  rw [h_terms]
  have h_add_pow : (∑ k ∈ Finset.range (Q + 1), (p * Real.exp t) ^ k * (1 - p) ^ (Q - k) *
      (Nat.choose Q k : ℝ)) = (p * Real.exp t + (1 - p)) ^ Q := by
    rw [add_pow]
  rw [h_add_pow, ← mul_pow]
  have h_inside : Real.exp (-t * p) * (p * Real.exp t + (1 - p)) =
      p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-t * p) := by
    have h_exp_add : Real.exp (-t * p) * Real.exp t = Real.exp (t * (1 - p)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (-t * p) * (p * Real.exp t + (1 - p)) =
          p * (Real.exp (-t * p) * Real.exp t) + (1 - p) * Real.exp (-t * p) := by ring
      _ = p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-t * p) := by rw [h_exp_add]
  rw [h_inside]
  have h_base := hoeffding_bernoulli_mgf p hp0 hp1 t
  have h_base_nonneg : 0 ≤ p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-t * p) := by
    positivity
  have h1 := pow_le_pow_left₀ h_base_nonneg h_base Q
  have h2 := (Real.exp_nat_mul (t ^ 2 / 8) Q).symm
  rw [h2] at h1
  exact h1

lemma binom_weighted_sum_lower (Q : ℕ) (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ k ∈ Finset.range (Q + 1), (Nat.choose Q k : ℝ) * p ^ k * (1 - p) ^ (Q - k) *
      Real.exp (t * ((Q : ℝ) * p - (k : ℝ))) ≤ Real.exp ((Q : ℝ) * (t ^ 2 / 8)) := by
  have h_exp_term : ∀ k : ℕ, Real.exp (t * ((Q : ℝ) * p - (k : ℝ))) =
      (Real.exp (t * p)) ^ Q * (Real.exp (-t)) ^ k := by
    intro k
    have h1 : t * ((Q : ℝ) * p - (k : ℝ)) = (k : ℝ) * (-t) + (Q : ℝ) * (t * p) := by ring
    rw [h1, Real.exp_add]
    have hk : Real.exp ((k : ℝ) * (-t)) = (Real.exp (-t)) ^ k := Real.exp_nat_mul (-t) k
    have hQ : Real.exp ((Q : ℝ) * (t * p)) = (Real.exp (t * p)) ^ Q := Real.exp_nat_mul (t * p) Q
    rw [hk, hQ, mul_comm]
  have h_terms : (∑ k ∈ Finset.range (Q + 1), (Nat.choose Q k : ℝ) * p ^ k * (1 - p) ^ (Q - k) *
      Real.exp (t * ((Q : ℝ) * p - (k : ℝ)))) =
      (Real.exp (t * p)) ^ Q * ∑ k ∈ Finset.range (Q + 1), (p * Real.exp (-t)) ^ k * (1 - p) ^ (Q - k) *
        (Nat.choose Q k : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h_exp_term k]
    ring
  rw [h_terms]
  have h_add_pow : (∑ k ∈ Finset.range (Q + 1), (p * Real.exp (-t)) ^ k * (1 - p) ^ (Q - k) *
      (Nat.choose Q k : ℝ)) = (p * Real.exp (-t) + (1 - p)) ^ Q := by
    rw [add_pow]
  rw [h_add_pow, ← mul_pow]
  have h_inside : Real.exp (t * p) * (p * Real.exp (-t) + (1 - p)) =
      p * Real.exp ((-t) * (1 - p)) + (1 - p) * Real.exp (-(-t) * p) := by
    have h_exp_add : Real.exp (t * p) * Real.exp (-t) = Real.exp ((-t) * (1 - p)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (t * p) * (p * Real.exp (-t) + (1 - p)) =
          p * (Real.exp (t * p) * Real.exp (-t)) + (1 - p) * Real.exp (t * p) := by ring
      _ = p * Real.exp ((-t) * (1 - p)) + (1 - p) * Real.exp (-(-t) * p) := by
        rw [h_exp_add]
        have h_eq : -(-t) * p = t * p := by
          ring
        rw [h_eq]
  rw [h_inside]
  have h_base := hoeffding_bernoulli_mgf p hp0 hp1 (-t)
  have h_base_nonneg : 0 ≤ p * Real.exp ((-t) * (1 - p)) + (1 - p) * Real.exp (-(-t) * p) := by
    positivity
  have h1 := pow_le_pow_left₀ h_base_nonneg h_base Q
  have h_neg_sq : (-t) ^ 2 / 8 = t ^ 2 / 8 := by ring
  rw [h_neg_sq] at h1
  have h2 := (Real.exp_nat_mul (t ^ 2 / 8) Q).symm
  rw [h2] at h1
  exact h1

/-- Exponential Chernoff–Hoeffding tail bound for the binomial distribution:
$\mathbb{P}(|S_Q / Q - p| \ge \varepsilon) \le 2 e^{-2 Q \varepsilon^2}$. -/
theorem binomTailProb_le_two_mul_exp (Q : ℕ) (hQ : 0 < Q) {p ε : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) :
    binomTailProb Q p ε ≤ 2 * Real.exp (-2 * (Q : ℝ) * ε ^ 2) := by
  by_cases hε_zero : ε = 0
  · subst hε_zero
    rw [binomTailProb_zero]
    have : -2 * (Q : ℝ) * (0 : ℝ) ^ 2 = 0 := by ring
    rw [this, Real.exp_zero, mul_one]
    linarith
  have hε_pos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε_zero)
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  let S := (Finset.range (Q + 1)).filter (fun (k : ℕ) => |(k : ℝ) / (Q : ℝ) - p| ≥ ε)
  let S1 := (Finset.range (Q + 1)).filter (fun (k : ℕ) => (Q : ℝ) * ε ≤ (k : ℝ) - (Q : ℝ) * p)
  let S2 := (Finset.range (Q + 1)).filter (fun (k : ℕ) => (Q : ℝ) * ε ≤ (Q : ℝ) * p - (k : ℝ))
  have hS_sub : S ⊆ S1 ∪ S2 := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hk_range : k ∈ Finset.range (Q + 1) := hk.1
    have hk_abs : ε ≤ |(k : ℝ) / (Q : ℝ) - p| := hk.2
    have hk_mul : (Q : ℝ) * ε ≤ |(k : ℝ) - (Q : ℝ) * p| := by
      calc
        (Q : ℝ) * ε ≤ (Q : ℝ) * |(k : ℝ) / (Q : ℝ) - p| := by
          exact mul_le_mul_of_nonneg_left hk_abs (le_of_lt hQ_pos)
        _ = |(Q : ℝ) * ((k : ℝ) / (Q : ℝ) - p)| := by
          have h_abs : (Q : ℝ) * |(k : ℝ) / (Q : ℝ) - p| = |(Q : ℝ)| * |(k : ℝ) / (Q : ℝ) - p| := by
            rw [abs_of_pos hQ_pos]
          rw [h_abs, ← abs_mul]
        _ = |(k : ℝ) - (Q : ℝ) * p| := by
          congr 1
          rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hQ_pos)]
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_total 0 ((k : ℝ) - (Q : ℝ) * p) with hpos | hneg
    · rw [abs_of_nonneg hpos] at hk_mul
      exact Or.inl ⟨hk_range, hk_mul⟩
    · rw [abs_of_nonpos hneg] at hk_mul
      have : -((k : ℝ) - (Q : ℝ) * p) = (Q : ℝ) * p - (k : ℝ) := by ring
      rw [this] at hk_mul
      exact Or.inr ⟨hk_range, hk_mul⟩
  let term := fun (k : ℕ) => (Nat.choose Q k : ℝ) * p ^ k * (1 - p) ^ (Q - k)
  have h_term_nonneg : ∀ k, 0 ≤ term k := fun k => by positivity
  have h_sum_le : binomTailProb Q p ε ≤ (∑ k ∈ S1, term k) + (∑ k ∈ S2, term k) := by
    unfold binomTailProb
    have h1 : (∑ k ∈ S, term k) ≤ ∑ k ∈ S1 ∪ S2, term k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hS_sub ?_
      intro k _ _
      exact h_term_nonneg k
    have h_inter : 0 ≤ ∑ k ∈ S1 ∩ S2, term k :=
      Finset.sum_nonneg fun k _ => h_term_nonneg k
    have h_u : (∑ k ∈ S1 ∪ S2, term k) + ∑ k ∈ S1 ∩ S2, term k = (∑ k ∈ S1, term k) + ∑ k ∈ S2, term k :=
      Finset.sum_union_inter
    have h2 : (∑ k ∈ S1 ∪ S2, term k) ≤ (∑ k ∈ S1, term k) + (∑ k ∈ S2, term k) := by
      linarith
    exact le_trans h1 h2
  let t := 4 * ε
  have ht_pos : 0 < t := by positivity
  have hS1_bound : (∑ k ∈ S1, term k) ≤ Real.exp (-2 * (Q : ℝ) * ε ^ 2) := by
    have h_elem : ∀ k ∈ S1, term k ≤
        Real.exp (-4 * (Q : ℝ) * ε ^ 2) * (term k * Real.exp (t * ((k : ℝ) - (Q : ℝ) * p))) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have ht_mul : 4 * (Q : ℝ) * ε ^ 2 ≤ t * ((k : ℝ) - (Q : ℝ) * p) := by
        calc
          4 * (Q : ℝ) * ε ^ 2 = t * ((Q : ℝ) * ε) := by
            dsimp [t]
            ring
          _ ≤ t * ((k : ℝ) - (Q : ℝ) * p) := by
            exact mul_le_mul_of_nonneg_left hk.2 (le_of_lt ht_pos)
      have h_exp_ineq : 1 ≤ Real.exp (-4 * (Q : ℝ) * ε ^ 2) * Real.exp (t * ((k : ℝ) - (Q : ℝ) * p)) := by
        rw [← Real.exp_add]
        have h_add : 0 ≤ -4 * (Q : ℝ) * ε ^ 2 + t * ((k : ℝ) - (Q : ℝ) * p) := by
          linarith
        exact Real.one_le_exp h_add
      calc
        term k = 1 * term k := by ring
        _ ≤ (Real.exp (-4 * (Q : ℝ) * ε ^ 2) * Real.exp (t * ((k : ℝ) - (Q : ℝ) * p))) * term k := by
          refine mul_le_mul_of_nonneg_right h_exp_ineq (h_term_nonneg k)
        _ = Real.exp (-4 * (Q : ℝ) * ε ^ 2) * (term k * Real.exp (t * ((k : ℝ) - (Q : ℝ) * p))) := by ring
    have h_sum1 : (∑ k ∈ S1, term k) ≤
        ∑ k ∈ S1, Real.exp (-4 * (Q : ℝ) * ε ^ 2) * (term k * Real.exp (t * ((k : ℝ) - (Q : ℝ) * p))) :=
      Finset.sum_le_sum h_elem
    rw [← Finset.mul_sum] at h_sum1
    have h_sub_all : (∑ k ∈ S1, term k * Real.exp (t * ((k : ℝ) - (Q : ℝ) * p))) ≤
        ∑ k ∈ Finset.range (Q + 1), term k * Real.exp (t * ((k : ℝ) - (Q : ℝ) * p)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro k hk
        exact (Finset.mem_filter.mp hk).1
      · intro k _ _
        positivity
    have h_weighted := binom_weighted_sum_upper Q p t hp0 hp1
    have ht_sq : (Q : ℝ) * (t ^ 2 / 8) = 2 * (Q : ℝ) * ε ^ 2 := by
      dsimp [t]
      ring
    rw [ht_sq] at h_weighted
    have h_total : (∑ k ∈ S1, term k) ≤ Real.exp (-4 * (Q : ℝ) * ε ^ 2) * Real.exp (2 * (Q : ℝ) * ε ^ 2) := by
      refine le_trans h_sum1 (mul_le_mul_of_nonneg_left (le_trans h_sub_all h_weighted) (by positivity))
    rw [← Real.exp_add] at h_total
    have h_add_exp : -4 * (Q : ℝ) * ε ^ 2 + 2 * (Q : ℝ) * ε ^ 2 = -2 * (Q : ℝ) * ε ^ 2 := by ring
    rw [h_add_exp] at h_total
    exact h_total
  have hS2_bound : (∑ k ∈ S2, term k) ≤ Real.exp (-2 * (Q : ℝ) * ε ^ 2) := by
    have h_elem : ∀ k ∈ S2, term k ≤
        Real.exp (-4 * (Q : ℝ) * ε ^ 2) * (term k * Real.exp (t * ((Q : ℝ) * p - (k : ℝ)))) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have ht_mul : 4 * (Q : ℝ) * ε ^ 2 ≤ t * ((Q : ℝ) * p - (k : ℝ)) := by
        calc
          4 * (Q : ℝ) * ε ^ 2 = t * ((Q : ℝ) * ε) := by
            dsimp [t]
            ring
          _ ≤ t * ((Q : ℝ) * p - (k : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hk.2 (le_of_lt ht_pos)
      have h_exp_ineq : 1 ≤ Real.exp (-4 * (Q : ℝ) * ε ^ 2) * Real.exp (t * ((Q : ℝ) * p - (k : ℝ))) := by
        rw [← Real.exp_add]
        have h_add : 0 ≤ -4 * (Q : ℝ) * ε ^ 2 + t * ((Q : ℝ) * p - (k : ℝ)) := by
          linarith
        exact Real.one_le_exp h_add
      calc
        term k = 1 * term k := by ring
        _ ≤ (Real.exp (-4 * (Q : ℝ) * ε ^ 2) * Real.exp (t * ((Q : ℝ) * p - (k : ℝ)))) * term k := by
          refine mul_le_mul_of_nonneg_right h_exp_ineq (h_term_nonneg k)
        _ = Real.exp (-4 * (Q : ℝ) * ε ^ 2) * (term k * Real.exp (t * ((Q : ℝ) * p - (k : ℝ)))) := by ring
    have h_sum2 : (∑ k ∈ S2, term k) ≤
        ∑ k ∈ S2, Real.exp (-4 * (Q : ℝ) * ε ^ 2) * (term k * Real.exp (t * ((Q : ℝ) * p - (k : ℝ)))) :=
      Finset.sum_le_sum h_elem
    rw [← Finset.mul_sum] at h_sum2
    have h_sub_all : (∑ k ∈ S2, term k * Real.exp (t * ((Q : ℝ) * p - (k : ℝ)))) ≤
        ∑ k ∈ Finset.range (Q + 1), term k * Real.exp (t * ((Q : ℝ) * p - (k : ℝ))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro k hk
        exact (Finset.mem_filter.mp hk).1
      · intro k _ _
        positivity
    have h_weighted := binom_weighted_sum_lower Q p t hp0 hp1
    have ht_sq : (Q : ℝ) * (t ^ 2 / 8) = 2 * (Q : ℝ) * ε ^ 2 := by
      dsimp [t]
      ring
    rw [ht_sq] at h_weighted
    have h_total : (∑ k ∈ S2, term k) ≤ Real.exp (-4 * (Q : ℝ) * ε ^ 2) * Real.exp (2 * (Q : ℝ) * ε ^ 2) := by
      refine le_trans h_sum2 (mul_le_mul_of_nonneg_left (le_trans h_sub_all h_weighted) (by positivity))
    rw [← Real.exp_add] at h_total
    have h_add_exp : -4 * (Q : ℝ) * ε ^ 2 + 2 * (Q : ℝ) * ε ^ 2 = -2 * (Q : ℝ) * ε ^ 2 := by ring
    rw [h_add_exp] at h_total
    exact h_total
  linarith

noncomputable def cert100 : GenuineBounds.GenuineFiniteFluctuationCertificate :=
  GenuineBounds.mkGenuineCertificate 100 (by norm_num) 25 25 (by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hsqrt : 0 < Real.sqrt 100 := by
      rw [Real.sqrt_pos]
      norm_num
    have hlog : 0 < Real.log 100 := by
      apply Real.log_pos
      norm_num
    have hpos : 0 < 100 / (8 * Real.pi * Real.sqrt 100 * Real.log 100) := by
      positivity
    simp only [sub_self, abs_zero]
    exact le_of_lt hpos)

theorem one_le_primeCounting_100 : 1 ≤ Nat.primeCounting 100 := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have h2 : 2 ∈ Nat.primesLE 100 := by
    rw [Nat.mem_primesLE]
    exact ⟨by omega, Nat.prime_two⟩
  have hpos : 0 < (Nat.primesLE 100).card := Finset.card_pos.mpr ⟨2, h2⟩
  exact hpos

theorem cert100_bound_lt_one : cert100.bound < 1 := by
  change 100 / (8 * Real.pi * Real.sqrt 100 * Real.log 100) < 1
  have hsqrt : Real.sqrt 100 = 10 := by
    have hsq : (10 : ℝ) ^ 2 = 100 := by norm_num
    rw [← hsq, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hexp : Real.exp 1 < 100 := by
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have hlog : 1 < Real.log 100 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hexp
  have hdenom : 100 < 8 * Real.pi * 10 * Real.log 100 := by
    calc
      100 < (80 : ℝ) * 3 * 1 := by norm_num
      _ < 8 * Real.pi * 10 * Real.log 100 := by
        have : (80 : ℝ) * 3 * 1 = 8 * 3 * 10 * 1 := by ring
        rw [this]
        gcongr
  have hpos : 0 < 8 * Real.pi * 10 * Real.log 100 := by
    positivity
  rw [div_lt_iff₀ hpos]
  linarith

theorem cert100_beats_trivial_card : cert100.bound < (Nat.primeCounting 100 : ℝ) := by
  have h1 : cert100.bound < 1 := cert100_bound_lt_one
  have h2 : (1 : ℝ) ≤ (Nat.primeCounting 100 : ℝ) := by
    exact_mod_cast one_le_primeCounting_100
  exact lt_of_lt_of_le h1 h2

/-! ## Part 2 — Constructive Two-Sided Erdős–Chebyshev Prime Bounds -/

/-- Primorial product bound: the product of primes up to `n` is at most `4 ^ n`. -/
theorem primorial_product_le_four_pow (n : ℕ) :
    ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ≤ 4 ^ n := by
  change primorial n ≤ 4 ^ n
  exact primorial_le_four_pow n

/-- Chebyshev's first function $\vartheta(n) = \sum_{p \le n} \log p$. -/
noncomputable def chebyshevTheta (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ)

/-- Linear upper bound on Chebyshev's $\vartheta(n) \le (2 \log 2) n$. -/
theorem chebyshevTheta_le_linear (n : ℕ) :
    chebyshevTheta n ≤ (2 * Real.log 2) * (n : ℝ) := by
  by_cases hn : n = 0
  · subst hn
    have h : (Finset.range (0 + 1)).filter Nat.Prime = ∅ := by
      rw [zero_add]
      exact Nat.primesLE_zero
    unfold chebyshevTheta
    rw [h, Finset.sum_empty]
    simp
  have hS_pos : ∀ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (0 : ℝ) < (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp_prime : Nat.Prime p := hp.2
    exact_mod_cast hp_prime.pos
  have h_log_prod : chebyshevTheta n =
      Real.log ((∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p : ℕ) : ℝ) := by
    simp only [chebyshevTheta]
    rw [← Real.log_prod]
    · congr 1
      exact (Nat.cast_prod _ _).symm
    · intro p hp
      exact ne_of_gt (hS_pos p hp)
  have h_prod_pos : 0 < ((∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p : ℕ) : ℝ) := by
    rw [Nat.cast_pos]
    exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
  have h_le : ((∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p : ℕ) : ℝ) ≤ (4 ^ n : ℝ) := by
    exact_mod_cast primorial_product_le_four_pow n
  rw [h_log_prod]
  have h_log_le : Real.log ((∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p : ℕ) : ℝ) ≤
      Real.log ((4 : ℝ) ^ n) := by
    exact Real.log_le_log h_prod_pos h_le
  refine le_trans h_log_le ?_
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [Real.log_pow, h4, Real.log_pow]
  ring_nf
  rfl

/-- Erdős–Chebyshev prime counting upper bound:
$\pi(n) \le \sqrt{n} + \frac{4 \log 2}{\log n} n$ for $n \ge 4$. -/
theorem primeCounting_le_chebyshev_upper (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ Real.sqrt n + (4 * Real.log 2) * (n : ℝ) / Real.log n := by
  have hn_pos : 0 < n := by
    linarith [hn]
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_pos
  have hlog_n_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    have hn1 : 1 < n := by
      linarith [hn]
    exact_mod_cast hn1
  let S := (Finset.range (n + 1)).filter Nat.Prime
  have hS_card : S.card = Nat.primeCounting n := by
    change (Nat.primesLE n).card = Nat.primeCounting n
    exact Nat.primesLE_card_eq_primeCounting n
  let k := Nat.sqrt n
  let S1 := S.filter (fun p => p ≤ k)
  let S2 := S.filter (fun p => k < p)
  have hS_union : S = S1 ∪ S2 := by
    ext p
    simp only [S1, S2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      obtain hle | hgt := le_or_gt p k
      · exact Or.inl ⟨hp, hle⟩
      · exact Or.inr ⟨hp, hgt⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩)
      · exact hp
      · exact hp
  have hS_disj : Disjoint S1 S2 := by
    rw [Finset.disjoint_filter]
    intro p _ hp1 hp2
    omega
  have hcard_sum : (S.card : ℝ) = (S1.card : ℝ) + (S2.card : ℝ) := by
    rw [hS_union, Finset.card_union_of_disjoint hS_disj]
    push_cast
    rfl
  have hS1_sub : S1 ⊆ Finset.Icc 1 k := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp.1).2
    have hp_ge : 1 ≤ p := hp_prime.one_le
    have hp_le : p ≤ k := hp.2
    exact Finset.mem_Icc.mpr ⟨hp_ge, hp_le⟩
  have hS1_card : (S1.card : ℝ) ≤ (k : ℝ) := by
    have hle := Finset.card_le_card hS1_sub
    rw [Nat.card_Icc] at hle
    have hsub : k + 1 - 1 = k := by omega
    rw [hsub] at hle
    exact_mod_cast hle
  have hk_le_sqrt : (k : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hk_sq : k ^ 2 ≤ n := Nat.sqrt_le' n
    have hk_sq_real : (k : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hk_sq
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    rw [← Real.sqrt_sq hk_nonneg]
    exact Real.sqrt_le_sqrt hk_sq_real
  have hS1_bound : (S1.card : ℝ) ≤ Real.sqrt (n : ℝ) :=
    le_trans hS1_card hk_le_sqrt
  have hS2_elem : ∀ p ∈ S2, Real.log (n : ℝ) / 2 ≤ Real.log (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp_gt_k : k < p := hp.2
    have hn_lt_p2 : n < p ^ 2 := (Nat.sqrt_lt' (m := n) (n := p)).mp hp_gt_k
    have hn_lt_p2_real : (n : ℝ) < (p : ℝ) ^ 2 := by exact_mod_cast hn_lt_p2
    have hp_pos : 0 < (p : ℝ) := by
      have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp.1).2
      exact_mod_cast hp_prime.pos
    have h_sqrt_lt_p : Real.sqrt (n : ℝ) < (p : ℝ) := by
      have h1 := Real.sqrt_lt_sqrt (by positivity) hn_lt_p2_real
      rw [Real.sqrt_sq (by positivity)] at h1
      exact h1
    have h_log_lt : Real.log (Real.sqrt (n : ℝ)) < Real.log (p : ℝ) :=
      Real.log_lt_log (Real.sqrt_pos.mpr hn_real_pos) h_sqrt_lt_p
    rw [Real.log_sqrt (by positivity)] at h_log_lt
    exact le_of_lt h_log_lt
  have hS2_sum : (S2.card : ℝ) * (Real.log (n : ℝ) / 2) ≤ chebyshevTheta n := by
    have h1 : (S2.card : ℝ) * (Real.log (n : ℝ) / 2) =
        ∑ _p ∈ S2, (Real.log (n : ℝ) / 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    rw [h1]
    have h2 : ∑ p ∈ S2, (Real.log (n : ℝ) / 2) ≤ ∑ p ∈ S2, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum fun p hp => hS2_elem p hp
    refine le_trans h2 ?_
    have h3 : ∑ p ∈ S2, Real.log (p : ℝ) ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro p hp
        exact (Finset.mem_filter.mp hp).1
      · intro p hp _
        have hp_pos : 1 ≤ (p : ℝ) := by
          have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp).2
          exact_mod_cast hp_prime.one_le
        exact Real.log_nonneg hp_pos
    exact h3
  have htheta_bound : chebyshevTheta n ≤ (2 * Real.log 2) * (n : ℝ) :=
    chebyshevTheta_le_linear n
  have hS2_mult : (S2.card : ℝ) * (Real.log (n : ℝ) / 2) ≤ (2 * Real.log 2) * (n : ℝ) :=
    le_trans hS2_sum htheta_bound
  have hS2_bound : (S2.card : ℝ) ≤ (4 * Real.log 2) * (n : ℝ) / Real.log (n : ℝ) := by
    have h_div : (S2.card : ℝ) * (Real.log (n : ℝ) / 2) * 2 / Real.log (n : ℝ) ≤
        (2 * Real.log 2) * (n : ℝ) * 2 / Real.log (n : ℝ) := by
      gcongr
    have h_cancel : (S2.card : ℝ) * (Real.log (n : ℝ) / 2) * 2 / Real.log (n : ℝ) =
        (S2.card : ℝ) := by
      calc
        (S2.card : ℝ) * (Real.log (n : ℝ) / 2) * 2 / Real.log (n : ℝ) =
            (S2.card : ℝ) * (Real.log (n : ℝ) / 2 * 2) / Real.log (n : ℝ) := by ring
        _ = (S2.card : ℝ) * Real.log (n : ℝ) / Real.log (n : ℝ) := by
          congr 1
          ring
        _ = (S2.card : ℝ) := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hlog_n_pos)]
    rw [h_cancel] at h_div
    have h_rhs : (2 * Real.log 2) * (n : ℝ) * 2 / Real.log (n : ℝ) =
        (4 * Real.log 2) * (n : ℝ) / Real.log (n : ℝ) := by ring
    rw [h_rhs] at h_div
    exact h_div
  rw [← hS_card, hcard_sum]
  linarith

/-- Upper bound on central binomial coefficient via prime counting:
$\binom{2n}{n} \le (2n)^{\pi(2n)}$ for $n \ge 1$. -/
lemma centralBinom_le_pow_primeCounting (n : ℕ) (hn : 1 ≤ n) :
    Nat.centralBinom n ≤ (2 * n) ^ (Nat.primeCounting (2 * n)) := by
  have hn2_pos : 0 < 2 * n := by
    linarith [hn]
  have h_ne : Nat.centralBinom n ≠ 0 := Nat.centralBinom_ne_zero n
  have h_sub : (Nat.centralBinom n).primeFactors ⊆ Nat.primesLE (2 * n) := by
    intro p hp
    have hp_ne_zero : (Nat.centralBinom n).factorization p ≠ 0 := by
      rwa [← Nat.support_factorization, Finsupp.mem_support_iff] at hp
    have hp_le : p ≤ 2 * n := by
      by_contra hgt
      have hgt' : 2 * n < p := not_le.mp hgt
      have h0 := Nat.factorization_centralBinom_eq_zero_of_two_mul_lt hgt'
      exact hp_ne_zero h0
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    rw [Nat.mem_primesLE]
    exact ⟨hp_le, hp_prime⟩
  have h_step1 : (Nat.centralBinom n) ≤
      ∏ p ∈ Nat.primesLE (2 * n), p ^ ((Nat.centralBinom n).factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization h_ne]
    refine Finset.prod_le_prod_of_subset_of_one_le (N := ℕ) h_sub ?_
    intro p _ hp_not_mem
    have h0 : (Nat.centralBinom n).factorization p = 0 := by
      by_contra hne
      have h_mem : p ∈ (Nat.centralBinom n).primeFactors := by
        rwa [← Nat.support_factorization, Finsupp.mem_support_iff]
      exact hp_not_mem h_mem
    rw [h0, pow_zero]
  have h_step2 : (∏ p ∈ Nat.primesLE (2 * n), p ^ ((Nat.centralBinom n).factorization p)) ≤
      ∏ _p ∈ Nat.primesLE (2 * n), (2 * n) := by
    refine Finset.prod_le_prod (N := ℕ) ?_
    intro p _
    exact Nat.pow_factorization_choose_le hn2_pos
  rw [Finset.prod_const, Nat.primesLE_card_eq_primeCounting] at h_step2
  exact le_trans h_step1 h_step2

/-- Erdős–Chebyshev prime counting lower bound via central binomial coefficient:
$\frac{n \log 4 - \log(2n + 1)}{\log(2n)} \le \pi(2n)$ for $n \ge 1$. -/
theorem erdos_chebyshev_primeCounting_lower (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) * Real.log 4 - Real.log (2 * (n : ℝ) + 1)) / Real.log (2 * (n : ℝ)) ≤
      (Nat.primeCounting (2 * n) : ℝ) := by
  have hn2_pos : 0 < 2 * n := by
    linarith [hn]
  have hn2_real_gt_one : 1 < (2 * (n : ℝ)) := by
    have : (2 : ℝ) ≤ 2 * (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    linarith
  have hlog_2n_pos : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos hn2_real_gt_one
  have h_binom_bound : 4 ^ n ≤ (2 * n + 1) * (2 * n) ^ (Nat.primeCounting (2 * n)) := by
    have h1 := Nat.four_pow_le_two_mul_add_one_mul_centralBinom n
    have h2 := centralBinom_le_pow_primeCounting n hn
    exact le_trans h1 (Nat.mul_le_mul_left (2 * n + 1) h2)
  have h_binom_real : (4 : ℝ) ^ n ≤ (2 * (n : ℝ) + 1) * (2 * (n : ℝ)) ^ (Nat.primeCounting (2 * n)) := by
    exact_mod_cast h_binom_bound
  have h_four_pow_pos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have h_prod_pos : 0 < (2 * (n : ℝ) + 1) * (2 * (n : ℝ)) ^ (Nat.primeCounting (2 * n)) := by
    refine mul_pos (by positivity) (by positivity)
  have h_log_le : Real.log ((4 : ℝ) ^ n) ≤
      Real.log ((2 * (n : ℝ) + 1) * (2 * (n : ℝ)) ^ (Nat.primeCounting (2 * n))) :=
    Real.log_le_log h_four_pow_pos h_binom_real
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h_log_le
  have h_sub : (n : ℝ) * Real.log 4 - Real.log (2 * (n : ℝ) + 1) ≤
      (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) := by
    linarith
  rw [div_le_iff₀ hlog_2n_pos]
  exact h_sub

/-- Asymptotic zero density of the primes: $\pi(n) / n \to 0$ as $n \to \infty$. -/
theorem primeCounting_div_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
  have h_sqrt_lim : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / Real.sqrt (n : ℝ)) Filter.atTop (nhds 0) := by
    have h_nat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have h_comp : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp h_nat
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_comp
  have h_log_lim : Filter.Tendsto (fun n : ℕ => (4 * Real.log 2) / Real.log (n : ℝ)) Filter.atTop (nhds 0) := by
    have h_nat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have h_comp : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp h_nat
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_comp
  have h_sum_lim : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / Real.sqrt (n : ℝ) +
      (4 * Real.log 2) / Real.log (n : ℝ)) Filter.atTop (nhds 0) := by
    have h_add := h_sqrt_lim.add h_log_lim
    rw [add_zero] at h_add
    exact h_add
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum_lim ?_ ?_
  · refine Filter.Eventually.of_forall ?_
    intro n
    by_cases hn : n = 0
    · subst hn
      simp
    · positivity
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    have hn_pos : 0 < n := by omega
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (by omega : 1 < n)
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_real_pos
    have h_upper := primeCounting_le_chebyshev_upper n hn
    have h_div_le : (Nat.primeCounting n : ℝ) / (n : ℝ) ≤
        (Real.sqrt (n : ℝ) + (4 * Real.log 2) * (n : ℝ) / Real.log (n : ℝ)) / (n : ℝ) := by
      gcongr
    refine le_trans h_div_le ?_
    have h_split : (Real.sqrt (n : ℝ) + (4 * Real.log 2) * (n : ℝ) / Real.log (n : ℝ)) / (n : ℝ) =
        Real.sqrt (n : ℝ) / (n : ℝ) + ((4 * Real.log 2) * (n : ℝ) / Real.log (n : ℝ)) / (n : ℝ) := by
      ring
    rw [h_split]
    have h1 : Real.sqrt (n : ℝ) / (n : ℝ) = 1 / Real.sqrt (n : ℝ) := by
      have hsq : (n : ℝ) = (Real.sqrt (n : ℝ)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      conv_lhs =>
        rhs
        rw [hsq]
      rw [sq]
      have h_cancel : Real.sqrt (n : ℝ) / (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) =
          1 / Real.sqrt (n : ℝ) := by
        rw [mul_comm, ← div_div, div_self (ne_of_gt hsqrt_pos)]
      exact h_cancel
    have h2 : ((4 * Real.log 2) * (n : ℝ) / Real.log (n : ℝ)) / (n : ℝ) =
        (4 * Real.log 2) / Real.log (n : ℝ) := by
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
      have h_div_div : ((4 * Real.log 2) * (n : ℝ) / Real.log (n : ℝ)) / (n : ℝ) =
          (n : ℝ) * (4 * Real.log 2) / ((n : ℝ) * Real.log (n : ℝ)) := by
        rw [div_div]
        ring
      rw [h_div_div, mul_div_mul_left _ _ hne]
    rw [h1, h2]

end InfoGeometry.Arithmetic.ChebyshevPrimeAndHoeffdingBounds
