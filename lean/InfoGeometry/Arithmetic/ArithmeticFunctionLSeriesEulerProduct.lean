/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Portions adapted from Thomas Browning's RiemannMasullo project, Apache-2.0,
revision be5d4cb0356d48406eae83233d73c99085b9a038.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Arithmetic.LSeriesCoefficientwiseUniformConvergence

/-!
# Convergence bounds for arithmetic-function L-series Euler products

These are reusable analytic lemmas for `ArithmeticFunction ℂ`. They establish
submultiplicativity of absolute Dirichlet sums under convolution, uniform bounds
for finite Euler products, and summability of a coefficientwise eventual limit.
The coefficientwise limit theorem is conditional on its stated local summability,
factor bounds, and stabilization hypotheses; this file constructs none of those
data for Hecke characters.

The proofs are adapted from
`external_refs/riemann-masullo/RiemannMasullo/ForMathlib/NumberTheory/ArithmeticFunction/LFunction.lean`
(Apache-2.0, Thomas Browning, revision
`be5d4cb0356d48406eae83233d73c99085b9a038`) and are checked against the pinned
Mathlib in this checkout.
-/

public section

open Filter Finset Function ArithmeticFunction

namespace InfoGeometry.Arithmetic.ArithmeticFunctionLSeriesEulerProduct

/-- The absolute Dirichlet sum is submultiplicative under arithmetic-function
Dirichlet convolution. -/
theorem tsum_norm_LSeries_term_mul_le {f g : ArithmeticFunction ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    ∑' n, ‖LSeries.term ⇑(f * g) s n‖ ≤
      (∑' n, ‖LSeries.term f s n‖) * ∑' n, ‖LSeries.term g s n‖ := by
  let t (p : ℕ × ℕ) := ‖LSeries.term f s p.1‖ * ‖LSeries.term g s p.2‖
  have ht : Summable t :=
    hf.norm.mul_of_nonneg hg.norm (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  let m (p : ℕ × ℕ) := p.1 * p.2
  have hsum : HasSum (fun n ↦ ∑' p : m ⁻¹' {n}, t p.val)
      ((∑' n, ‖LSeries.term f s n‖) * ∑' n, ‖LSeries.term g s n‖) :=
    (hf.norm.hasSum.mul hg.norm.hasSum ht).tsum_fiberwise m
  rw [← hsum.tsum_eq]
  apply (LSeriesSummable_mul hf hg).norm.tsum_le_tsum _ hsum.summable
  intro n
  rw [← ArithmeticFunction.coe_mul, LSeries.term_convolution']
  apply tsum_of_norm_bounded (ht.subtype (fun p ↦ m p = n)).hasSum
  intro p
  exact (norm_mul _ _).le

/-- Absolute Dirichlet sums of finite convolution products are bounded by the
product of the supplied exponential local bounds. -/
theorem LSeries_finset_prod_bound {ι : Type*} (f : ι → ArithmeticFunction ℂ) (s : ℂ)
    {u : ι → ℝ} (hf : ∀ i, LSeriesSummable (f i) s)
    (hb : ∀ i, (∑' n, ‖LSeries.term (f i) s n‖) ≤ Real.exp (u i)) (S : Finset ι) :
    LSeriesSummable ⇑(∏ i ∈ S, f i) s ∧
      (∑' n, ‖LSeries.term ⇑(∏ i ∈ S, f i) s n‖) ≤ Real.exp (∑ i ∈ S, u i) := by
  classical
  have hone (n : ℕ) : LSeries.term ⇑(1 : ArithmeticFunction ℂ) s n =
      if n = 1 then 1 else 0 := by
    by_cases hn : n = 1 <;> simp [LSeries.term, hn]
  have hnorm : HasSum (fun n ↦ ‖LSeries.term ⇑(1 : ArithmeticFunction ℂ) s n‖) 1 := by
    simpa [hone, apply_ite] using (hasSum_ite_eq (1 : ℕ) (1 : ℝ))
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, Finset.sum_empty, Real.exp_zero, LSeriesSummable] using
      And.intro hnorm.summable.of_norm hnorm.tsum_eq.le
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Real.exp_add]
    exact ⟨LSeriesSummable_mul (hf i) ih.1,
      (tsum_norm_LSeries_term_mul_le (hf i) ih.1).trans
        (mul_le_mul (hb i) ih.2 (tsum_nonneg fun _ ↦ norm_nonneg _) (Real.exp_pos _).le)⟩

/-- Uniform absolute-sum bounds for finite products imply summability of their
coefficientwise eventual limit. -/
theorem LSeriesSummable_of_eventuallyEq_finset_prod {ι : Type*}
    (f : ι → ArithmeticFunction ℂ) (g : ArithmeticFunction ℂ) (s : ℂ)
    {u : ι → ℝ} (hu : Summable u) (hu₀ : ∀ i, 0 ≤ u i)
    (hf : ∀ i, LSeriesSummable (f i) s)
    (hb : ∀ i, (∑' n, ‖LSeries.term (f i) s n‖) ≤ Real.exp (u i))
    (he : ∀ n, ∀ᶠ S : Finset ι in atTop, (∏ i ∈ S, f i) n = g n) :
    LSeriesSummable g s := by
  classical
  have hprod := LSeries_finset_prod_bound f s hf hb
  apply Summable.of_norm
  apply summable_of_sum_le (c := Real.exp (∑' i, u i)) (fun _ ↦ norm_nonneg _)
  intro T
  obtain ⟨S, hS⟩ := ((Filter.eventually_all_finset T).mpr (fun n _ ↦ he n)).exists
  calc
    ∑ n ∈ T, ‖LSeries.term g s n‖ =
        ∑ n ∈ T, ‖LSeries.term ⇑(∏ i ∈ S, f i) s n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [LSeries.term, hS n hn]
    _ ≤ ∑' n, ‖LSeries.term ⇑(∏ i ∈ S, f i) s n‖ :=
      (hprod S).1.norm.sum_le_tsum T fun _ _ ↦ norm_nonneg _
    _ ≤ Real.exp (∑' i, u i) :=
      (hprod S).2.trans (Real.exp_le_exp.mpr (hu.sum_le_tsum S (fun i _ ↦ hu₀ i)))

/-- At prime-power indices, the Dirichlet terms of a geometric local power
series are powers of one complex number; all other coefficients vanish. -/
theorem LSeries_term_geometric_ofPowerSeries {q : ℕ} (hq : 1 < q) (a s : ℂ) :
    let f := ArithmeticFunction.ofPowerSeries q (PowerSeries.mk fun k ↦ a ^ k)
    (∀ k : ℕ, LSeries.term f s (q ^ k) = (a * (q : ℂ) ^ (-s)) ^ k) ∧
    ∀ n : ℕ, n ∉ Set.range (q ^ · : ℕ → ℕ) → LSeries.term f s n = 0 := by
  dsimp only
  constructor
  · intro k
    rw [LSeries.term_of_ne_zero (pow_ne_zero k (Nat.ne_zero_of_lt hq)),
      ofPowerSeries_apply_pow hq,
      PowerSeries.coeff_mk, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
      Complex.cpow_nat_mul, Complex.cpow_neg, mul_pow, inv_pow, div_eq_mul_inv]
  · intro n hn
    simp [LSeries.term, ofPowerSeries_apply hq, Function.extend_apply' _ _ _ hn]

/-- The absolute Dirichlet sum for a geometric local power series is the
corresponding real geometric series whenever the ratio has norm below one. -/
theorem hasSum_norm_LSeries_term_ofPowerSeries {q : ℕ} (hq : 1 < q) {a s : ℂ}
    (h : ‖a * (q : ℂ) ^ (-s)‖ < 1) :
    HasSum (fun n ↦ ‖LSeries.term (ArithmeticFunction.ofPowerSeries q
      (PowerSeries.mk fun k ↦ a ^ k)) s n‖) (1 - ‖a * (q : ℂ) ^ (-s)‖)⁻¹ := by
  obtain ⟨hpow, hout⟩ := LSeries_term_geometric_ofPowerSeries hq a s
  apply (Nat.pow_right_injective hq).hasSum_iff (fun n hn ↦ by simp [hout n hn]) |>.mp
  apply (hasSum_geometric_of_lt_one (norm_nonneg _) h).congr_fun
  intro k
  simp [Function.comp_apply, hpow]

/-- A finite Dirichlet convolution product sums to the product of the local
series sums. -/
theorem LSeriesHasSum_finset_prod {ι : Type*} (f : ι → ArithmeticFunction ℂ)
    (a : ι → ℂ) (s : ℂ) (h : ∀ i, LSeriesHasSum (f i) s (a i)) (S : Finset ι) :
    LSeriesHasSum ⇑(∏ i ∈ S, f i) s (∏ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    have hone (n : ℕ) : LSeries.term ⇑(1 : ArithmeticFunction ℂ) s n =
        if n = 1 then 1 else 0 := by
      by_cases hn : n = 1 <;> simp [LSeries.term, hn]
    simpa only [LSeriesHasSum, funext hone] using hasSum_ite_eq (1 : ℕ) (1 : ℂ)
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ArithmeticFunction.LSeriesHasSum_mul (h i) ih

/-- Finite Dirichlet-convolution Euler products converge uniformly on each closed
right half-plane when their coefficients stabilize and their local absolute sums
have a summable family of uniform exponential bounds. -/
theorem LSeries_finset_prod_tendstoUniformlyOn_of_eventuallyEq {ι : Type*}
    (f : ι → ArithmeticFunction ℂ) (g : ArithmeticFunction ℂ) {r a : ℝ}
    {u : ι → ℝ} (hra : r < a) (hu : Summable u) (hu₀ : ∀ i, 0 ≤ u i)
    (hf : ∀ i, LSeriesSummable (f i) (r : ℂ))
    (hb : ∀ i, (∑' n, ‖LSeries.term (f i) (r : ℂ) n‖) ≤ Real.exp (u i))
    (he : ∀ n, ∀ᶠ S : Finset ι in atTop, (∏ i ∈ S, f i) n = g n) :
    TendstoUniformlyOn
      (fun S s ↦ LSeries (fun n ↦ (∏ i ∈ S, f i) n) s)
      (LSeries (g : ℕ → ℂ)) atTop {s : ℂ | a ≤ s.re} := by
  have hg : LSeriesSummable (g : ℕ → ℂ) (r : ℂ) :=
    LSeriesSummable_of_eventuallyEq_finset_prod f g (r : ℂ) hu hu₀ hf hb he
  apply InfoGeometry.Arithmetic.LSeriesCoefficientwiseUniformConvergence.tendstoUniformlyOn_LSeries_of_eventuallyEq
    (f := fun S n ↦ (∏ i ∈ S, f i) n) (g := (g : ℕ → ℂ))
    (r := r) (a := a) (C := Real.exp (∑' i, u i)) hra
    (le_of_lt (Real.exp_pos _))
  · intro S
    exact (LSeries_finset_prod_bound f (r : ℂ) hf hb S).1
  · exact hg
  · intro S
    exact ((LSeries_finset_prod_bound f (r : ℂ) hf hb S).2).trans
      (Real.exp_le_exp.mpr (hu.sum_le_tsum S (fun i _ ↦ hu₀ i)))
  · exact he

end InfoGeometry.Arithmetic.ArithmeticFunctionLSeriesEulerProduct
