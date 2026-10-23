/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.WeakValuePoleCriterion
import Mathlib.Tactic

/-!
# Derivative residue in the same parameter as a weak-value pole

Contract: for complex-valued numerator and denominator on a real parameter,
a simple denominator zero and continuous first derivatives imply that the
scaled derivative of the quotient tends to the negative residue. We reuse
the owner's denominator-slope limit and isolation theorem. This concerns the
actual derivative in that parameter; it does not identify an independent
spatial derivative or assert a fluid equation. The real-part theorem tracks
the real residue, so a purely imaginary residue is not misclassified.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeakValueDerivativePole

open Filter Set WeakValuePoleCriterion
open scoped Topology

/-- A simple quotient pole differentiates to a quadratic pole when the first
derivatives are continuous. Differentiability is needed only locally. -/
theorem tendsto_scaled_derivative {n d n' d' : ℝ → ℂ} {t0 : ℝ}
    (hn : ∀ᶠ t in 𝓝 t0, HasDerivAt n (n' t) t)
    (hd : ∀ᶠ t in 𝓝 t0, HasDerivAt d (d' t) t)
    (hnc : ContinuousAt n' t0) (hdc : ContinuousAt d' t0)
    (hd0 : d t0 = 0) (hc : d' t0 ≠ 0) :
    Tendsto (fun t => ((t - t0 : ℝ) : ℂ) ^ 2 * deriv (fun s => n s / d s) t)
      (𝓝[≠] t0) (𝓝 (-(n t0 / d' t0))) := by
  have hn0 := hn.self_of_nhds
  have hdAt := hd.self_of_nhds
  have hnlim : Tendsto n (𝓝[≠] t0) (𝓝 (n t0)) :=
    hn0.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hdlim : Tendsto d (𝓝[≠] t0) (𝓝 (d t0)) :=
    hdAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hn'lim : Tendsto n' (𝓝[≠] t0) (𝓝 (n' t0)) :=
    hnc.tendsto.mono_left nhdsWithin_le_nhds
  have hd'lim : Tendsto d' (𝓝[≠] t0) (𝓝 (d' t0)) :=
    hdc.tendsto.mono_left nhdsWithin_le_nhds
  have hslope := tendsto_denominator_slope hd0 hdAt
  have hlim := ((hn'lim.mul hdlim).sub (hnlim.mul hd'lim)).div
    (hslope.pow 2) (pow_ne_zero 2 hc)
  have hvalue : (n' t0 * d t0 - n t0 * d' t0) / d' t0 ^ 2 =
      -(n t0 / d' t0) := by
    rw [hd0]
    field_simp
    ring
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds,
    hd.filter_mono nhdsWithin_le_nhds,
    eventually_denominator_ne_zero hd0 hdAt hc,
    (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[≠] t0, t ∈ ({t0} : Set ℝ)ᶜ)]
    with t hnt hdt hdt0 ht
  have ht0 : t - t0 ≠ 0 := sub_ne_zero.mpr (by simpa using ht)
  have htC : ((t - t0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
  change (n' t * d t - n t * d' t) / (d t / ((t - t0 : ℝ) : ℂ)) ^ 2 =
    ((t - t0 : ℝ) : ℂ) ^ 2 * deriv (fun s => n s / d s) t
  have hquot := hnt.div hdt hdt0
  change HasDerivAt (fun s => n s / d s) _ t at hquot
  rw [hquot.deriv]
  field_simp

/-- The derivative of the real readout has the negative real residue. -/
theorem tendsto_scaled_real_derivative {n d n' d' : ℝ → ℂ} {t0 : ℝ}
    (hn : ∀ᶠ t in 𝓝 t0, HasDerivAt n (n' t) t)
    (hd : ∀ᶠ t in 𝓝 t0, HasDerivAt d (d' t) t)
    (hnc : ContinuousAt n' t0) (hdc : ContinuousAt d' t0)
    (hd0 : d t0 = 0) (hc : d' t0 ≠ 0) :
    Tendsto (fun t => (t - t0) ^ 2 * deriv (fun s => (n s / d s).re) t)
      (𝓝[≠] t0) (𝓝 (-(n t0 / d' t0).re)) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (tendsto_scaled_derivative hn hd hnc hdc hd0 hc)
  simp only [Function.comp_def, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul, Complex.neg_re] at h
  apply h.congr'
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds,
    hd.filter_mono nhdsWithin_le_nhds,
    eventually_denominator_ne_zero hd0 hd.self_of_nhds hc] with t hnt hdt ht
  have hquot := hnt.div hdt ht
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hquot
  change HasDerivAt (fun s => n s / d s) _ t at hquot
  change HasDerivAt (fun s => (n s / d s).re) _ t at hreal
  rw [hquot.deriv, hreal.deriv]
  rfl

/-- Nonzero real residue forces a quadratic lower bound for the derivative
in the same parameter, on the regular punctured domain. -/
theorem eventually_abs_derivative_lower_bound {n d n' d' : ℝ → ℂ} {t0 : ℝ}
    (hn : ∀ᶠ t in 𝓝 t0, HasDerivAt n (n' t) t)
    (hd : ∀ᶠ t in 𝓝 t0, HasDerivAt d (d' t) t)
    (hnc : ContinuousAt n' t0) (hdc : ContinuousAt d' t0)
    (hd0 : d t0 = 0) (hc : d' t0 ≠ 0)
    (hr : (n t0 / d' t0).re ≠ 0) :
    ∀ᶠ t in 𝓝[≠] t0, d t ≠ 0 ∧
      (|(n t0 / d' t0).re| / 2) / (t - t0) ^ 2 ≤
        |deriv (fun s => (n s / d s).re) t| := by
  have hpos : 0 < |(n t0 / d' t0).re| := abs_pos.mpr hr
  have hlim := (tendsto_scaled_real_derivative hn hd hnc hdc hd0 hc).abs
  rw [abs_neg] at hlim
  have hlarge := hlim.eventually_const_lt (by linarith :
    |(n t0 / d' t0).re| / 2 < |(n t0 / d' t0).re|)
  filter_upwards [hlarge, eventually_denominator_ne_zero hd0 hd.self_of_nhds hc,
    (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[≠] t0, t ∈ ({t0} : Set ℝ)ᶜ)]
    with t ht hdt ht0
  have hsq : 0 < (t - t0) ^ 2 := sq_pos_of_ne_zero
    (sub_ne_zero.mpr (by simpa using ht0))
  refine ⟨hdt, (div_le_iff₀ hsq).mpr ?_⟩
  simpa only [abs_mul, abs_of_nonneg (sq_nonneg (t - t0)), mul_comm] using ht.le

end InfoGeometry.Canonical.WeakValueDerivativePole
