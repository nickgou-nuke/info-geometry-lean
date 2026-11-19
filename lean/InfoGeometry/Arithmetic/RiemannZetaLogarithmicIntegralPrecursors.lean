/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.GenuineBounds
import InfoGeometry.Arithmetic.ChebyshevPrimeAndHoeffdingBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open scoped Interval
open MeasureTheory Filter Topology

/-!
# Riemann-Zeta and Logarithmic Integral Precursors

This module establishes the core calculus and asymptotic analysis of the logarithmic integral
`GenuineBounds.li` and its connections to Chebyshev prime counting bounds and the Riemann zeta
pole divergence at `s = 1`.

The 12 target theorems establish:
1. `li_two`: Base point evaluation `li 2 = 0`.
2. `continuousOn_one_div_log`: Continuity of `1 / log t` on `[2, ∞)`.
3. `intervalIntegrable_one_div_log`: Interval integrability of `1 / log t` on `[2, x]`.
4. `hasDerivAt_li`: FTC derivative `li'(x) = 1 / log x` for `x > 2`.
5. `li_pos`: Strict positivity `li x > 0` for `x > 2`.
6. `hasDerivAt_id_div_log`: Derivative `(u / log u)' = 1 / log t - 1 / (log t)^2`.
7. `fundamental_li_by_parts`: Integration by parts expansion `li x = x / log x - 2 / log 2 + ∫ 1 / (log t)^2`.
8. `li_sub_div_log_pos`: Positivity of remainder `li x - (x / log x - 2 / log 2) > 0`.
9. `integral_one_div_log_sq_le`: Uniform upper bound on the remainder integral.
10. `li_le_linear_over_log_sq`: Two-sided asymptotic upper bound for `li x`.
11. `primeCounting_le_chebyshev_li`: Constructive bridge connecting Chebyshev prime count to `li n`.
12. `tendsto_riemannZeta_one_right_atTop`: Real-pole divergence `Re(ζ(σ)) → +∞` as `σ → 1⁺`.
-/

namespace InfoGeometry.Arithmetic.RiemannZetaLogarithmicIntegralPrecursors

/-- Evaluation of the logarithmic integral at its basepoint `x = 2`. -/
theorem li_two : GenuineBounds.li 2 = 0 := by
  dsimp [GenuineBounds.li]
  exact intervalIntegral.integral_same

/-- Continuity of `t ↦ 1 / log t` on `[2, ∞)`. -/
theorem continuousOn_one_div_log : ContinuousOn (fun t => 1 / Real.log t) (Set.Ici 2) := by
  refine continuousOn_const.div ?_ ?_
  · exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [show (2 : ℝ) ≤ t from ht]))
  · intro t ht
    have ht1 : 1 < t := by linarith [show (2 : ℝ) ≤ t from ht]
    exact ne_of_gt (Real.log_pos ht1)

/-- Interval integrability of `t ↦ 1 / log t` on `[2, x]` for `2 ≤ x`. -/
theorem intervalIntegrable_one_div_log (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume 2 x :=
  ContinuousOn.intervalIntegrable_of_Icc hx
    (continuousOn_one_div_log.mono (fun _t ht => ht.1))

/-- Auxiliary continuity of `t ↦ 1 / log t` on `(1, ∞)`. -/
lemma continuousOn_one_div_log_Ioi :
    ContinuousOn (fun t => 1 / Real.log t) (Set.Ioi 1) := by
  refine continuousOn_const.div ?_ ?_
  · exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [show (1 : ℝ) < t from ht]))
  · intro t ht
    exact ne_of_gt (Real.log_pos ht)

/-- Fundamental Theorem of Calculus: the logarithmic integral has derivative `1 / log x` for `x > 2`. -/
theorem hasDerivAt_li (x : ℝ) (hx : 2 < x) :
    HasDerivAt GenuineBounds.li (1 / Real.log x) x := by
  have hx1 : 1 < x := by linarith
  have hx2 : 2 ≤ x := le_of_lt hx
  have h_int : IntervalIntegrable (fun t => 1 / Real.log t) volume 2 x :=
    intervalIntegrable_one_div_log x hx2
  have h_meas : StronglyMeasurableAtFilter (fun t => 1 / Real.log t) (𝓝 x) := by
    refine ⟨Set.Ioi 1, IsOpen.mem_nhds isOpen_Ioi hx1, ?_⟩
    exact continuousOn_one_div_log_Ioi.aestronglyMeasurable isOpen_Ioi.measurableSet
  have h_cont : ContinuousAt (fun t => 1 / Real.log t) x :=
    continuousOn_one_div_log_Ioi.continuousAt (IsOpen.mem_nhds isOpen_Ioi hx1)
  exact intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont

/-- Strict positivity of the logarithmic integral `li(x) > 0` for `x > 2`. -/
theorem li_pos (x : ℝ) (hx : 2 < x) : 0 < GenuineBounds.li x := by
  have h_cont : ContinuousOn (fun t => 1 / Real.log t) (Set.Icc 2 x) :=
    continuousOn_one_div_log.mono (fun _t ht => ht.1)
  have h_le : ∀ t ∈ Set.Ioc 2 x, 0 ≤ 1 / Real.log t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact div_nonneg (by norm_num) (le_of_lt (Real.log_pos ht1))
  have h_lt : ∃ c ∈ Set.Icc 2 x, 0 < 1 / Real.log c := by
    refine ⟨2, ⟨le_rfl, le_of_lt hx⟩, ?_⟩
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_pos (by norm_num) this
  exact intervalIntegral.integral_pos hx h_cont h_le h_lt

/-- Derivative of `u ↦ u / log u` via quotient rule. -/
theorem hasDerivAt_id_div_log (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun u => u / Real.log u) (1 / Real.log t - 1 / (Real.log t) ^ 2) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht])
  have hlog_pos : 0 < Real.log t := Real.log_pos ht
  have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
  have h1 : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id' t
  have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
  have hdiv := h1.div h2 hlog_ne
  have heq : ((1 * Real.log t - t * t⁻¹) / (Real.log t) ^ 2) =
      (1 / Real.log t - 1 / (Real.log t) ^ 2) := by
    have ht_inv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    rw [ht_inv, one_mul]
    have hlog_sq : (Real.log t) ^ 2 = Real.log t * Real.log t := by ring
    rw [sub_div, hlog_sq]
    congr 1
    have : Real.log t = Real.log t * 1 := (mul_one _).symm
    nth_rewrite 1 [this]
    exact mul_div_mul_left (1 : ℝ) (Real.log t) hlog_ne
  rw [heq] at hdiv
  exact hdiv

/-- Continuity of `t ↦ 1 / (log t)^2` on `[2, ∞)`. -/
lemma continuousOn_one_div_log_sq :
    ContinuousOn (fun t => 1 / (Real.log t) ^ 2) (Set.Ici 2) := by
  refine continuousOn_const.div ?_ ?_
  · exact (Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [show (2 : ℝ) ≤ t from ht]))).pow 2
  · intro t ht
    have ht1 : 1 < t := by linarith [show (2 : ℝ) ≤ t from ht]
    exact pow_ne_zero 2 (ne_of_gt (Real.log_pos ht1))

/-- Interval integrability of `t ↦ 1 / (log t)^2` on `[2, x]` for `2 ≤ x`. -/
lemma intervalIntegrable_one_div_log_sq (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => 1 / (Real.log t) ^ 2) MeasureTheory.volume 2 x :=
  ContinuousOn.intervalIntegrable_of_Icc hx
    (continuousOn_one_div_log_sq.mono (fun _t ht => ht.1))

/-- Fundamental integration-by-parts identity for `li(x)`. -/
theorem fundamental_li_by_parts (x : ℝ) (hx : 2 ≤ x) :
    GenuineBounds.li x = x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 := by
  have hcont : ContinuousOn (fun u => u / Real.log u) (Set.Icc 2 x) := by
    refine continuousOn_id.div ?_ ?_
    · exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [ht.1]))
    · intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      exact ne_of_gt (Real.log_pos ht1)
  have hderiv : ∀ u ∈ Set.Ioo 2 x, HasDerivAt (fun u => u / Real.log u) (1 / Real.log u - 1 / (Real.log u) ^ 2) u := by
    intro u hu
    have hu1 : 1 < u := by linarith [hu.1]
    exact hasDerivAt_id_div_log u hu1
  have hint : IntervalIntegrable (fun u => 1 / Real.log u - 1 / (Real.log u) ^ 2) volume 2 x :=
    (intervalIntegrable_one_div_log x hx).sub (intervalIntegrable_one_div_log_sq x hx)
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx hcont hderiv hint
  have h_sub := intervalIntegral.integral_sub (intervalIntegrable_one_div_log x hx) (intervalIntegrable_one_div_log_sq x hx)
  rw [h_sub] at h_ftc
  change GenuineBounds.li x - (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) = x / Real.log x - 2 / Real.log 2 at h_ftc
  linarith

/-- Positivity of the remainder `li(x) - (x / log x - 2 / log 2) > 0` for `x > 2`. -/
theorem li_sub_div_log_pos (x : ℝ) (hx : 2 < x) :
    0 < GenuineBounds.li x - (x / Real.log x - 2 / Real.log 2) := by
  have h_by_parts := fundamental_li_by_parts x (le_of_lt hx)
  have h_cont : ContinuousOn (fun t => 1 / (Real.log t) ^ 2) (Set.Icc 2 x) :=
    continuousOn_one_div_log_sq.mono (fun _t ht => ht.1)
  have h_le : ∀ t ∈ Set.Ioc 2 x, 0 ≤ 1 / (Real.log t) ^ 2 := by
    intro t _ht
    exact div_nonneg (by norm_num) (sq_nonneg _)
  have h_lt : ∃ c ∈ Set.Icc 2 x, 0 < 1 / (Real.log c) ^ 2 := by
    refine ⟨2, ⟨le_rfl, le_of_lt hx⟩, ?_⟩
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_pos (by norm_num) (sq_pos_of_pos this)
  have h_int_pos := intervalIntegral.integral_pos hx h_cont h_le h_lt
  linarith

/-- Uniform upper bound on the integration-by-parts remainder integral. -/
theorem integral_one_div_log_sq_le (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) ≤ (x - 2) / (Real.log 2) ^ 2 := by
  have h_mono : (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) ≤ ∫ t in (2 : ℝ)..x, 1 / (Real.log 2) ^ 2 := by
    refine intervalIntegral.integral_mono_on hx (intervalIntegrable_one_div_log_sq x hx)
      (continuous_const.intervalIntegrable 2 x) ?_
    intro t ht
    have ht2 : 2 ≤ t := ht.1
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog_le : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hsq_pos : 0 < (Real.log 2) ^ 2 := sq_pos_of_pos hlog2_pos
    have hsq_le : (Real.log 2) ^ 2 ≤ (Real.log t) ^ 2 := by
      nlinarith [hlog2_pos, hlog_le]
    exact one_div_le_one_div_of_le hsq_pos hsq_le
  have h_const : (∫ _ in (2 : ℝ)..x, (1 / (Real.log 2) ^ 2)) = (x - 2) / (Real.log 2) ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one_div]
  linarith

/-- Explicit upper bound for `li(x)` with linear remainder over `(log 2)^2`. -/
theorem li_le_linear_over_log_sq (x : ℝ) (hx : 2 ≤ x) :
    GenuineBounds.li x ≤ x / Real.log x - 2 / Real.log 2 + (x - 2) / (Real.log 2) ^ 2 := by
  have h1 := fundamental_li_by_parts x hx
  have h2 := integral_one_div_log_sq_le x hx
  linarith

/-- Constructive upper bound for prime counting `π(n)` in terms of `li(n)`. -/
theorem primeCounting_le_chebyshev_li (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ Real.sqrt n + (4 * Real.log 2) * (GenuineBounds.li n + 2 / Real.log 2) := by
  have h_cheb := ChebyshevPrimeAndHoeffdingBounds.primeCounting_le_chebyshev_upper n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
    norm_cast
    omega
  have h_parts := fundamental_li_by_parts (n : ℝ) hn2
  have hint_nonneg : 0 ≤ ∫ t in (2 : ℝ)..(n : ℝ), 1 / (Real.log t) ^ 2 := by
    refine intervalIntegral.integral_nonneg hn2 ?_
    intro t _ht
    exact div_nonneg (by norm_num) (sq_nonneg _)
  have h_div_le : (n : ℝ) / Real.log (n : ℝ) ≤ GenuineBounds.li (n : ℝ) + 2 / Real.log 2 := by
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4log2_pos : 0 ≤ 4 * Real.log 2 := by linarith
  have h_term_le : (4 * Real.log 2) * (n : ℝ) / Real.log (n : ℝ) ≤
      (4 * Real.log 2) * (GenuineBounds.li (n : ℝ) + 2 / Real.log 2) := by
    have : (4 * Real.log 2) * (n : ℝ) / Real.log (n : ℝ) = (4 * Real.log 2) * ((n : ℝ) / Real.log (n : ℝ)) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h_div_le h4log2_pos
  linarith

/-- Real-pole divergence of the Riemann zeta function: `Re(ζ(σ)) → +∞` as `σ → 1⁺`. -/
theorem tendsto_riemannZeta_one_right_atTop :
    Filter.Tendsto (fun σ : ℝ => (riemannZeta (σ : ℂ)).re) (𝓝[>] 1) Filter.atTop := by
  have h_asymp := ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
  have h_re := (Complex.continuous_re.tendsto (Real.eulerMascheroniConstant : ℂ)).comp h_asymp
  have hre_eq : ∀ s : ℝ, (riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)).re =
      (riemannZeta (s : ℂ)).re - 1 / (s - 1) := by
    intro s
    rw [Complex.sub_re]
    congr 1
    have h1 : (1 : ℂ) / ((s : ℂ) - 1) = Complex.ofReal (1 / (s - 1)) := by
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_sub]
    rw [h1, Complex.ofReal_re]
  have h_re' : Tendsto (fun s : ℝ => (riemannZeta (s : ℂ)).re - 1 / (s - 1)) (𝓝[>] 1) (𝓝 Real.eulerMascheroniConstant) := by
    refine h_re.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s _hs
    exact hre_eq s
  have h_sub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun s : ℝ => s - 1) 1 :=
        continuous_id.sub continuous_const |>.continuousAt
      have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 0) := by
        simpa using hcont.tendsto
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      exact sub_pos.mpr hs
  have h_div_top : Tendsto (fun s : ℝ => 1 / (s - 1)) (𝓝[>] 1) atTop := by
    have h_inv := Filter.Tendsto.inv_tendsto_nhdsGT_zero h_sub
    refine h_inv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s _hs
    exact (one_div (s - 1)).symm
  have h_add := Filter.Tendsto.atTop_add h_div_top h_re'
  refine h_add.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _hs
  ring

end InfoGeometry.Arithmetic.RiemannZetaLogarithmicIntegralPrecursors
