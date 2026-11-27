/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.SmoothedMangoldtReal
import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform

/-!
# Mellin integrals of the smoothed von Mangoldt sum

On the half-plane `1 < re s`, the actual real-cutoff smoothed sum has
Mellin integral `(-ζ'(s) / ζ(s)) / (s * (s - 1))`. Centering subtracts
the transform of `x log x` and adds `(1 + gamma)` times the transform of `x`.

The proof uses Mathlib's absolutely convergent von Mangoldt L-series and
its partial-sum integral theorem twice. Integrability is proved separately,
so none of the displayed integrals relies on the default value assigned to
a nonintegrable Bochner integral. This file proves no Landau continuation
theorem and no zero-free statement beyond the convergent half-plane.
-/

noncomputable section

open Finset Filter MeasureTheory Asymptotics Complex
open scoped Topology LSeries.notation
open ArithmeticFunction

namespace InfoGeometry.Arithmetic.PrimeDistributionLaw

private theorem sum_norm_isBigO_of_LSeriesSummable {f : ℕ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hf : LSeriesSummable f (r : ℂ)) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ‖f n‖) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r) := by
  have hnorm : Summable (fun n => ‖LSeries.term f (r : ℂ) n‖) := hf.norm
  refine IsBigO.of_bound (∑' n, ‖LSeries.term f (r : ℂ) n‖) ?_
  refine Filter.Eventually.of_forall fun N => ?_
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) r)]
  calc
    (∑ n ∈ Finset.Icc 1 N, ‖f n‖) ≤
        ∑ n ∈ Finset.Icc 1 N, ‖LSeries.term f (r : ℂ) n‖ * (N : ℝ) ^ r := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      calc
        ‖f n‖ = ‖LSeries.term f (r : ℂ) n‖ * (n : ℝ) ^ r := by
          rw [LSeries.norm_term_eq, ite_eq_right hn0, Complex.ofReal_re]
          exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hnpos r).ne').symm
        _ ≤ ‖LSeries.term f (r : ℂ) n‖ * (N : ℝ) ^ r := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact Real.rpow_le_rpow (Nat.cast_nonneg n)
            (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hr
    _ = (∑ n ∈ Finset.Icc 1 N, ‖LSeries.term f (r : ℂ) n‖) * (N : ℝ) ^ r := by
      rw [Finset.sum_mul]
    _ ≤ (∑' n, ‖LSeries.term f (r : ℂ) n‖) * (N : ℝ) ^ r := by
      exact mul_le_mul_of_nonneg_right
        (hnorm.sum_le_tsum (Finset.Icc 1 N) (fun _ _ => norm_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg N) r)

private theorem partialSum_mul_cpow_integrable {f : ℕ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ‖f n‖) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r)) :
    IntegrableOn
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) * (x : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) := by
  have hC : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r) :=
    (isBigO_of_le _ fun _ => (norm_sum_le _ _).trans (Real.le_norm_self _)).trans hO
  have hR : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) =O[atTop]
      (fun x : ℝ => x ^ r) :=
    (hC.comp_tendsto tendsto_nat_floor_atTop).trans
      (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))
  have hloc : LocallyIntegrableOn
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) * (x : ℂ) ^ (-(s + 1)))
      (Set.Ici 1) := by
    simp_rw [mul_comm]
    apply locallyIntegrableOn_mul_sum_Icc f zero_le_one
    refine ContinuousOn.locallyIntegrableOn (fun x hx => ?_) measurableSet_Ici
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le hx).ne')).continuousWithinAt
  have hpow : (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) =O[atTop]
      (fun x : ℝ => x ^ (-(s + 1)).re) :=
    (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.of_norm_left
  have hb : (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) * (x : ℂ) ^ (-(s + 1))) =O[atTop]
      (fun x : ℝ => x ^ (r - s.re - 1)) := by
    exact hR.mul_atTop_rpow_of_isBigO_rpow r (-(s + 1)).re (r - s.re - 1) hpow
      (by simp only [neg_re, add_re, one_re]; linarith)
  exact (hloc.integrableOn_of_isBigO_atTop hb
    (integrableAtFilter_rpow_atTop_iff.mpr (by linarith [hs]))).mono_set Set.Ioi_subset_Ici_self

private theorem term_div_nat_shift (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun k => f k / (k : ℂ)) (s - 1) n = LSeries.term f s n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_sub s 1 hnC, Complex.cpow_one]
    exact div_div_div_cancel_right₀ hnC _ _

private theorem mul_cpow_neg_sub_one {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  calc
    (x : ℂ) * (x : ℂ) ^ (-(s + 1)) =
        (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-(s + 1)) := by rw [Complex.cpow_one]
    _ = (x : ℂ) ^ ((1 : ℂ) + (-(s + 1))) := (Complex.cpow_add _ _ hxC).symm
    _ = (x : ℂ) ^ (-s) := by congr 1; ring

private theorem realSmoothedMangoldtSum_complex_eq (x : ℝ) :
    (realSmoothedMangoldtSum x : ℂ) =
      (x : ℂ) * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) / (n : ℂ)) -
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) := by
  rw [realSmoothedMangoldtSum_eq_Icc]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [vonMangoldtWeight]
  ring

/-- The smoothed von Mangoldt integral converges absolutely and equals the actual
negative logarithmic derivative of zeta divided by the two Mellin factors. -/
theorem realSmoothedMangoldtSum_mellin {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
        (fun x : ℝ => (realSmoothedMangoldtSum x : ℂ) * (x : ℂ) ^ (-(s + 1)))
        (Set.Ioi 1) ∧
      (∫ x : ℝ in Set.Ioi 1,
        (realSmoothedMangoldtSum x : ℂ) * (x : ℂ) ^ (-(s + 1))) =
        ActualRiemannZetaVonMangoldtBridge.actualRiemannZetaLogDerivative s /
          (s * (s - 1)) := by
  let r : ℝ := (s.re + 1) / 2
  have hr1 : 1 < r := by dsimp [r]; linarith
  have hrs : r < s.re := by dsimp [r]; linarith
  let a : ℕ → ℂ := fun n => (Λ n : ℂ) / (n : ℂ)
  have hBsum : LSeriesSummable (fun n => (Λ n : ℂ)) (r : ℂ) :=
    LSeriesSummable_vonMangoldt (by simpa using hr1)
  have hAsum : LSeriesSummable a ((r - 1 : ℝ) : ℂ) := by
    have hcast : ((r - 1 : ℝ) : ℂ) = (r : ℂ) - 1 := by push_cast; rfl
    rw [hcast]
    change Summable (fun n => LSeries.term a ((r : ℂ) - 1) n)
    simpa only [a, term_div_nat_shift] using
      (show Summable (fun n => LSeries.term (fun k => (Λ k : ℂ)) (r : ℂ) n) from hBsum)
  have hBO := sum_norm_isBigO_of_LSeriesSummable (le_of_lt (zero_lt_one.trans hr1)) hBsum
  have hAO := sum_norm_isBigO_of_LSeriesSummable (sub_nonneg.mpr hr1.le) hAsum
  have hBI := partialSum_mul_cpow_integrable (le_of_lt (zero_lt_one.trans hr1)) hrs hBO
  have hAI : IntegrableOn
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-s))
      (Set.Ioi 1) := by
    simpa only [sub_add_cancel] using
      partialSum_mul_cpow_integrable (sub_nonneg.mpr hr1.le)
        (s := s - 1) (by simp only [sub_re, one_re]; linarith) hAO
  have hB := LSeries_eq_mul_integral' (fun n => (Λ n : ℂ))
    (le_of_lt (zero_lt_one.trans hr1)) hrs hBO
  have hA : LSeries (fun n => (Λ n : ℂ)) s = (s - 1) *
      ∫ x : ℝ in Set.Ioi 1,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-s) := by
    simpa only [LSeries, a, term_div_nat_shift, sub_add_cancel] using
      LSeries_eq_mul_integral' a (sub_nonneg.mpr hr1.le)
        (s := s - 1) (by simp only [sub_re, one_re]; linarith) hAO
  have hsplit (x : ℝ) (hx : x ∈ Set.Ioi (1 : ℝ)) :
      (realSmoothedMangoldtSum x : ℂ) * (x : ℂ) ^ (-(s + 1)) =
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-s) -
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ)) * (x : ℂ) ^ (-(s + 1)) := by
    rw [realSmoothedMangoldtSum_complex_eq]
    change ((x : ℂ) * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) -
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ)) * (x : ℂ) ^ (-(s + 1)) = _
    calc
      _ = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) *
          ((x : ℂ) * (x : ℂ) ^ (-(s + 1))) -
          (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ)) * (x : ℂ) ^ (-(s + 1)) := by ring
      _ = _ := by rw [mul_cpow_neg_sub_one (zero_lt_one.trans hx)]
  refine ⟨(integrableOn_congr_fun hsplit measurableSet_Ioi).mpr (hAI.sub hBI), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hAI hBI]
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs1 : s - 1 ≠ 0 :=
    Complex.ne_zero_of_re_pos (by simp only [sub_re, one_re]; linarith)
  have hA' : (∫ x : ℝ in Set.Ioi 1,
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-s)) =
      LSeries (fun n => (Λ n : ℂ)) s / (s - 1) := by
    apply (eq_div_iff hs1).mpr
    simpa [mul_comm] using hA.symm
  have hB' : (∫ x : ℝ in Set.Ioi 1,
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ)) * (x : ℂ) ^ (-(s + 1))) =
      LSeries (fun n => (Λ n : ℂ)) s / s := by
    apply (eq_div_iff hs0).mpr
    simpa [mul_comm] using hB.symm
  rw [hA', hB',
    ActualRiemannZetaVonMangoldtBridge.vonMangoldt_LSeries_eq_actualRiemannZetaLogDerivative hs]
  field_simp [hs0, hs1]
  ring

private def unitTail : ℝ → ℂ := (Set.Ioi 1).indicator (fun _ => 1)

private theorem unitTail_hasMellin {z : ℂ} (hz : z.re < 0) :
    HasMellin unitTail z (-1 / z) := by
  have hz' : (z - 1).re < -1 := by simp only [sub_re, one_re]; linarith [hz]
  have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi zero_le_one
  simp_rw [HasMellin, mellin, MellinConvergent, unitTail, ← Set.indicator_smul,
    IntegrableOn, integrable_indicator_iff measurableSet_Ioi, smul_eq_mul,
    integral_indicator measurableSet_Ioi, mul_one, IntegrableOn,
    Measure.restrict_restrict_of_subset hsub]
  refine ⟨integrableOn_Ioi_cpow_of_lt hz' zero_lt_one, ?_⟩
  rw [integral_Ioi_cpow_of_lt hz' zero_lt_one, ofReal_one, one_cpow, sub_add_cancel]

private theorem unitTail_log_mellin {z : ℂ} (hz : z.re < 0) :
    IntegrableOn
        (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (z - 1)) (Set.Ioi 1) ∧
      (∫ x : ℝ in Set.Ioi 1,
        (Real.log x : ℂ) * (x : ℂ) ^ (z - 1)) = 1 / z ^ 2 := by
  have hloc : LocallyIntegrableOn unitTail (Set.Ioi 0) :=
    ((locallyIntegrable_const (1 : ℂ)).indicator measurableSet_Ioi).locallyIntegrableOn _
  have htop : unitTail =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Set.Ioi (1 : ℝ) <;> simp [unitTail, hx]
  have hbot : unitTail =O[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => x ^ (-(z.re - 1))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with x hx
    simp [unitTail, Set.mem_Ioi, not_lt.mpr hx.le]
  obtain ⟨hlogint, hderiv⟩ := mellin_hasDerivAt_of_isBigO_rpow
    hloc htop hz hbot (by linarith : z.re - 1 < z.re)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hrat : HasDerivAt (fun w : ℂ => -1 / w) (1 / z ^ 2) z := by
    change HasDerivAt ((fun _ : ℂ => (-1 : ℂ)) / id) (1 / z ^ 2) z
    simpa using (hasDerivAt_const z (-1 : ℂ)).div (hasDerivAt_id z) hz0
  have heq : mellin unitTail =ᶠ[𝓝 z] (fun w : ℂ => -1 / w) := by
    filter_upwards [(Complex.continuous_re.tendsto z).eventually
      (eventually_lt_nhds hz)] with w hw
    exact (unitTail_hasMellin hw).2
  have hval := hderiv.unique (hrat.congr_of_eventuallyEq heq)
  have hlogfun : (fun x : ℝ => Real.log x • unitTail x) =
      (Set.Ioi 1).indicator (fun x : ℝ => (Real.log x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Ioi (1 : ℝ) <;> simp [unitTail, hx]
  rw [hlogfun] at hlogint hval
  have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi zero_le_one
  simp_rw [MellinConvergent, mellin, ← Set.indicator_smul,
    IntegrableOn, integrable_indicator_iff measurableSet_Ioi, smul_eq_mul,
    integral_indicator measurableSet_Ioi, IntegrableOn,
    Measure.restrict_restrict_of_subset hsub] at hlogint hval
  exact ⟨by simpa only [IntegrableOn, mul_comm] using hlogint,
    by simpa only [mul_comm] using hval⟩

private theorem log_mul_cpow_mellin {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
        (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-s)) (Set.Ioi 1) ∧
      (∫ x : ℝ in Set.Ioi 1,
        (Real.log x : ℂ) * (x : ℂ) ^ (-s)) = 1 / (s - 1) ^ 2 := by
  have hz : (1 - s).re < 0 := by simp only [sub_re, one_re]; linarith [hs]
  have h := unitTail_log_mellin hz
  have he : (1 : ℂ) - s - 1 = -s := by ring
  have hsq : ((1 : ℂ) - s) ^ 2 = (s - 1) ^ 2 := by ring
  simpa only [he, hsq] using h

/-- The centered sum has a genuine Mellin integral on the convergent half-plane.
The elementary centering terms are evaluated explicitly. -/
theorem centeredSmoothedMangoldtSum_mellin {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
        (fun x : ℝ => (centeredSmoothedMangoldtSum x : ℂ) * (x : ℂ) ^ (-(s + 1)))
        (Set.Ioi 1) ∧
      (∫ x : ℝ in Set.Ioi 1,
        (centeredSmoothedMangoldtSum x : ℂ) * (x : ℂ) ^ (-(s + 1))) =
        ActualRiemannZetaVonMangoldtBridge.actualRiemannZetaLogDerivative s /
            (s * (s - 1)) -
          1 / (s - 1) ^ 2 + (1 + (Real.eulerMascheroniConstant : ℂ)) / (s - 1) := by
  obtain ⟨hS, hSval⟩ := realSmoothedMangoldtSum_mellin hs
  obtain ⟨hlog, hlogval⟩ := log_mul_cpow_mellin hs
  have hpower : (-s).re < -1 := by simp only [neg_re]; linarith
  have hI := integrableOn_Ioi_cpow_of_lt hpower (c := (1 : ℝ)) zero_lt_one
  have hIval : (∫ x : ℝ in Set.Ioi 1, (x : ℂ) ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt hpower zero_lt_one, ofReal_one, one_cpow]
    have he : -s + 1 = -(s - 1) := by ring
    rw [he, neg_div_neg_eq]
  have hsplit (x : ℝ) (hx : x ∈ Set.Ioi (1 : ℝ)) :
      (centeredSmoothedMangoldtSum x : ℂ) * (x : ℂ) ^ (-(s + 1)) =
        (realSmoothedMangoldtSum x : ℂ) * (x : ℂ) ^ (-(s + 1)) -
        (Real.log x : ℂ) * (x : ℂ) ^ (-s) +
        (1 + (Real.eulerMascheroniConstant : ℂ)) * (x : ℂ) ^ (-s) := by
    unfold centeredSmoothedMangoldtSum
    push_cast
    have hpow := mul_cpow_neg_sub_one (zero_lt_one.trans hx) s
    calc
      _ = (realSmoothedMangoldtSum x : ℂ) * (x : ℂ) ^ (-(s + 1)) -
          (Real.log x : ℂ) * ((x : ℂ) * (x : ℂ) ^ (-(s + 1))) +
          (1 + (Real.eulerMascheroniConstant : ℂ)) *
            ((x : ℂ) * (x : ℂ) ^ (-(s + 1))) := by ring
      _ = _ := by rw [hpow]
  have hlinear := hI.const_mul (1 + (Real.eulerMascheroniConstant : ℂ))
  have hsub : IntegrableOn
      (fun x : ℝ => (realSmoothedMangoldtSum x : ℂ) * (x : ℂ) ^ (-(s + 1)) -
        (Real.log x : ℂ) * (x : ℂ) ^ (-s)) (Set.Ioi 1) := hS.sub hlog
  refine ⟨(integrableOn_congr_fun hsplit measurableSet_Ioi).mpr ((hS.sub hlog).add hlinear), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_add hsub hlinear, integral_sub hS hlog,
    integral_const_mul, hSval, hlogval, hIval]
  ring

end InfoGeometry.Arithmetic.PrimeDistributionLaw
