import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# A precise simple-pole criterion for the real part of a complex ratio

The numerator and denominator are actual complex-valued functions of a real
parameter. A simple zero of the denominator gives the complex residue
`n(t0)/d'(t0)`. A nonzero real part of that residue yields an explicit
punctured lower bound for the real readout. A nonzero complex numerator alone
does not imply this hypothesis.

The parameter can be spatial or temporal; this theorem does not identify it
with a fluid coordinate or infer an integral estimate.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeakValuePoleCriterion

open Filter Set
open scoped Topology

variable {n d : ℝ → ℂ} {t0 : ℝ} {c : ℂ}

/-- A two-state complex denominator requires its modulus, not a positive-density
square root. This is the actual derivative bound for the real ratio. -/
theorem abs_deriv_real_ratio_le {dn dd : ℂ}
    (hn : HasDerivAt n dn t0) (hd : HasDerivAt d dd t0) (h0 : d t0 ≠ 0) :
    |deriv (fun t => (n t / d t).re) t0| ≤
      ‖dn‖ / ‖d t0‖ + ‖n t0‖ * ‖dd‖ / ‖d t0‖ ^ 2 := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t0 (hn.div hd h0)
  change HasDerivAt (fun t => (n t / d t).re)
    ((dn * d t0 - n t0 * dd) / d t0 ^ 2).re t0 at h
  rw [h.deriv]
  have hnorm : ‖d t0‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  calc
    |((dn * d t0 - n t0 * dd) / d t0 ^ 2).re| ≤
        ‖(dn * d t0 - n t0 * dd) / d t0 ^ 2‖ := Complex.abs_re_le_norm _
    _ ≤ (‖dn‖ * ‖d t0‖ + ‖n t0‖ * ‖dd‖) / ‖d t0‖ ^ 2 := by
      rw [norm_div, norm_pow]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [norm_mul] using norm_sub_le (dn * d t0) (n t0 * dd)
    _ = ‖dn‖ / ‖d t0‖ + ‖n t0‖ * ‖dd‖ / ‖d t0‖ ^ 2 := by
      field_simp

theorem tendsto_denominator_slope (hd0 : d t0 = 0)
    (hd : HasDerivAt d c t0) :
    Tendsto (fun t => d t / ((t - t0 : ℝ) : ℂ)) (𝓝[≠] t0) (𝓝 c) := by
  have h := hd.tendsto_slope
  change Tendsto (fun t => (t - t0)⁻¹ • (d t - d t0)) (𝓝[≠] t0) (𝓝 c) at h
  simpa only [hd0, sub_zero, Complex.real_smul,
    Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using h

/-- A simple zero is isolated in a sufficiently small punctured neighborhood. -/
theorem eventually_denominator_ne_zero (hd0 : d t0 = 0)
    (hd : HasDerivAt d c t0) (hc : c ≠ 0) :
    ∀ᶠ t in 𝓝[≠] t0, d t ≠ 0 := by
  filter_upwards [(tendsto_denominator_slope hd0 hd).eventually_ne hc] with t ht
  intro hzero
  apply ht
  simp [hzero]

theorem tendsto_complex_residue (hd0 : d t0 = 0)
    (hd : HasDerivAt d c t0) (hc : c ≠ 0) (hn : ContinuousAt n t0) :
    Tendsto (fun t => ((t - t0 : ℝ) : ℂ) * (n t / d t))
      (𝓝[≠] t0) (𝓝 (n t0 / c)) := by
  have hn' : Tendsto n (𝓝[≠] t0) (𝓝 (n t0)) :=
    hn.tendsto.mono_left nhdsWithin_le_nhds
  have hq := hn'.div (tendsto_denominator_slope hd0 hd) hc
  have heq : (fun t => ((t - t0 : ℝ) : ℂ) * (n t / d t)) =
      (fun t => n t / (d t / ((t - t0 : ℝ) : ℂ))) := by
    funext t
    rw [div_div_eq_mul_div, mul_comm (n t), mul_div_assoc]
  rw [heq]
  exact hq

theorem tendsto_real_residue (hd0 : d t0 = 0)
    (hd : HasDerivAt d c t0) (hc : c ≠ 0) (hn : ContinuousAt n t0) :
    Tendsto (fun t => (t - t0) * (n t / d t).re)
      (𝓝[≠] t0) (𝓝 ((n t0 / c).re)) := by
  have h := (Complex.continuous_re.tendsto (n t0 / c)).comp
    (tendsto_complex_residue hd0 hd hc hn)
  simpa only [Function.comp_def, Complex.re_ofReal_mul] using h

/-- A nonzero real residue gives an inverse-distance lower bound on the
actual real readout, on a neighborhood where the denominator is nonzero. -/
theorem eventually_abs_readout_lower_bound (hd0 : d t0 = 0)
    (hd : HasDerivAt d c t0) (hc : c ≠ 0) (hn : ContinuousAt n t0)
    (hr : (n t0 / c).re ≠ 0) :
    ∀ᶠ t in 𝓝[≠] t0,
      d t ≠ 0 ∧
      (|(n t0 / c).re| / 2) / |t - t0| ≤ |(n t / d t).re| := by
  have hrpos : 0 < |(n t0 / c).re| := abs_pos.mpr hr
  have hhalf : |(n t0 / c).re| / 2 < |(n t0 / c).re| := by linarith
  have hlarge := (tendsto_real_residue hd0 hd hc hn).abs.eventually_const_lt hhalf
  filter_upwards [hlarge, eventually_denominator_ne_zero hd0 hd hc,
    (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[≠] t0, t ∈ ({t0} : Set ℝ)ᶜ)]
    with t ht hdt ht0
  have hne : t ≠ t0 := by simpa using ht0
  have hdist : 0 < |t - t0| := abs_pos.mpr (sub_ne_zero.mpr hne)
  refine ⟨hdt, (div_le_iff₀ hdist).mpr ?_⟩
  simpa only [abs_mul, mul_comm] using ht.le

end InfoGeometry.Canonical.WeakValuePoleCriterion
