import InfoGeometry.Arithmetic.BostConnesNativeZetaPartition

/-!
# Rescaled actual zeta pole asymptotic

The native zeta owner already proves the one-sided remainder asymptotic at the
real pole.  This file records its direct rescaled consequence.  It does not
assert the separate zero-temperature limit at `β → ∞`.
-/

open scoped Topology

noncomputable section

namespace InfoGeometry.Arithmetic.ActualZetaPoleAsymptoticBridge

open Filter
open InfoGeometry.Arithmetic.BostConnesNativeZetaPartition

theorem actualRiemannZeta_rescaled_pole_tendsto
    : Tendsto
        (fun β : ℝ => ((β - 1 : ℝ) : ℂ) * riemannZeta (β : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hrem := actualRiemannZeta_sub_one_div_tendsto_nhds_right
  have hreal : Tendsto (fun β : ℝ => β - 1)
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hid : Tendsto (fun β : ℝ => β)
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)))
  have hcomplex : Tendsto (fun β : ℝ => ((β - 1 : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa [Complex.ofReal_sub, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hprod : Tendsto
      (fun β : ℝ => ((β - 1 : ℝ) : ℂ) *
        (riemannZeta (β : ℂ) - 1 / ((β : ℂ) - 1)))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using hcomplex.mul hrem
  have hsum : Tendsto
      (fun β : ℝ => ((β - 1 : ℝ) : ℂ) *
        (riemannZeta (β : ℂ) - 1 / ((β : ℂ) - 1)) + 1)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using hprod.add tendsto_const_nhds
  have hdecomp :
      (fun β : ℝ => ((β - 1 : ℝ) : ℂ) * riemannZeta (β : ℂ)) =ᶠ[
        𝓝[>] (1 : ℝ)]
      (fun β : ℝ => ((β - 1 : ℝ) : ℂ) *
        (riemannZeta (β : ℂ) - 1 / ((β : ℂ) - 1)) + 1) := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    have hβ' : 1 < β := hβ
    have hne : (β : ℂ) - 1 ≠ 0 := by
      intro hz
      have : β - 1 = 0 := by
        exact_mod_cast congrArg Complex.re hz
      linarith
    push_cast
    field_simp [hne]
    ring
  exact hsum.congr' hdecomp.symm

theorem actualRiemannZeta_quadratically_rescaled_pole_tendsto
    : Tendsto
        (fun β : ℝ => ((β - 1 : ℝ) : ℂ) ^ 2 * riemannZeta (β : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
  have hzero : Tendsto
      (fun β : ℝ => ((β - 1 : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hid : Tendsto (fun β : ℝ => β)
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hreal : Tendsto (fun β : ℝ => β - 1)
        (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using hid.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)))
    simpa [Complex.ofReal_sub, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hlinear := actualRiemannZeta_rescaled_pole_tendsto
  have hprod := hzero.mul hlinear
  simpa [pow_two, mul_assoc] using hprod

theorem realPartitionSeries_quadratically_rescaled_pole_tendsto
    : Tendsto
        (fun β : ℝ => (β - 1) ^ 2 * realPartitionSeries β)
        (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply (Complex.continuous_re.continuousAt.tendsto.comp
    actualRiemannZeta_quadratically_rescaled_pole_tendsto).congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  rw [realPartitionSeries_eq_riemannZeta β hβ]
  change
    ((((β - 1 : ℝ) : ℂ) ^ 2 * riemannZeta (β : ℂ)).re) =
      (β - 1) ^ 2 * (riemannZeta (β : ℂ)).re
  have hcast :
      (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) := by
    norm_num
  have hre : (((β : ℂ) - 1) ^ 2).re = (β - 1) ^ 2 := by
    rw [hcast]
    norm_num [pow_two]
  have him : (((β : ℂ) - 1) ^ 2).im = 0 := by
    rw [hcast]
    norm_num [pow_two]
  rw [show (((β - 1 : ℝ) : ℂ) ^ 2) = ((β : ℂ) - 1) ^ 2 by
    rw [hcast]]
  simp [Complex.mul_re, hre, him]

theorem actualRiemannZeta_rescaled_pole_real_tendsto
    : Tendsto
        (fun β : ℝ => (β - 1) * (riemannZeta (β : ℂ)).re)
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  have h := actualRiemannZeta_rescaled_pole_tendsto
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa [Function.comp_def, Complex.mul_re, Complex.ofReal_sub] using hre

theorem realPartitionSeries_rescaled_pole_tendsto
    : Tendsto
        (fun β : ℝ => (β - 1) * realPartitionSeries β)
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  apply (actualRiemannZeta_rescaled_pole_real_tendsto).congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  rw [realPartitionSeries_eq_riemannZeta β hβ]

theorem realPartitionSeries_pole_lower_bound_eventually
    {c : ℝ} (hc1 : c < 1) :
    ∀ᶠ β : ℝ in 𝓝[>] (1 : ℝ),
      c / (β - 1) < realPartitionSeries β := by
  have hres := realPartitionSeries_rescaled_pole_tendsto
  have hq : ∀ᶠ β : ℝ in 𝓝[>] (1 : ℝ),
      c < (β - 1) * realPartitionSeries β := by
    apply hres.eventually
    exact isOpen_Ioi.mem_nhds hc1
  filter_upwards [self_mem_nhdsWithin, hq] with β hβ hqβ
  have hδ : 0 < β - 1 := sub_pos.mpr hβ
  apply (div_lt_iff₀ hδ).2
  simpa [mul_comm] using hqβ

theorem realPartitionSeries_pole_upper_bound_eventually
    {c : ℝ} (hc1 : 1 < c) :
    ∀ᶠ β : ℝ in 𝓝[>] (1 : ℝ),
      realPartitionSeries β < c / (β - 1) := by
  have hres := realPartitionSeries_rescaled_pole_tendsto
  have hq : ∀ᶠ β : ℝ in 𝓝[>] (1 : ℝ),
      (β - 1) * realPartitionSeries β < c := by
    exact hres.eventually (isOpen_Iio.mem_nhds hc1)
  filter_upwards [self_mem_nhdsWithin, hq] with β hβ hqβ
  have hδ : 0 < β - 1 := sub_pos.mpr hβ
  apply (lt_div_iff₀ hδ).2
  simpa [mul_comm] using hqβ

theorem realPartitionSeries_pole_two_sided_bound_eventually
    {cl cu : ℝ} (hcl : cl < 1) (hcu : 1 < cu) :
    ∀ᶠ β : ℝ in 𝓝[>] (1 : ℝ),
      cl / (β - 1) < realPartitionSeries β ∧
        realPartitionSeries β < cu / (β - 1) := by
  filter_upwards [realPartitionSeries_pole_lower_bound_eventually hcl,
    realPartitionSeries_pole_upper_bound_eventually hcu] with β hβl hβu
  exact ⟨hβl, hβu⟩

theorem realPartitionSeries_div_pole_model_tendsto
    : Tendsto
        (fun β : ℝ => realPartitionSeries β / (1 / (β - 1)))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  apply realPartitionSeries_rescaled_pole_tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβ' : 1 < β := hβ
  have hne : β - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hβ')
  calc
    (β - 1) * realPartitionSeries β =
        realPartitionSeries β * (β - 1) := by ring
    _ = realPartitionSeries β / (1 / (β - 1)) := by
      field_simp [hne]

theorem realPartitionSeries_log_rescaled_pole_tendsto
    : Tendsto
        (fun β : ℝ => Real.log ((β - 1) * realPartitionSeries β))
        (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hlog :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      realPartitionSeries_rescaled_pole_tendsto
  simpa using hlog

theorem realPartitionSeries_log_add_log_pole_model_eq_rescaled
    {β : ℝ} (hβ : 1 < β) :
    Real.log (realPartitionSeries β) + Real.log (β - 1) =
      Real.log ((β - 1) * realPartitionSeries β) := by
  rw [Real.log_mul (ne_of_gt (sub_pos.mpr hβ))
    (ne_of_gt (realPartitionSeries_pos β hβ))]
  ring

theorem realPartitionSeries_log_add_log_pole_model_tendsto
    : Tendsto
        (fun β : ℝ => Real.log (realPartitionSeries β) + Real.log (β - 1))
        (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply realPartitionSeries_log_rescaled_pole_tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact (realPartitionSeries_log_add_log_pole_model_eq_rescaled hβ).symm

theorem realPartitionSeries_tendsto_atTop_nhdsWithin_one_right :
    Tendsto realPartitionSeries (𝓝[>] (1 : ℝ)) atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  by_cases hb : b ≤ 0
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact hb.trans (le_of_lt (realPartitionSeries_pos β hβ))
  · have hbpos : 0 < b := lt_of_not_ge hb
    have hres := realPartitionSeries_rescaled_pole_tendsto
    have hq : ∀ᶠ β : ℝ in 𝓝[>] (1 : ℝ),
        (1 / 2 : ℝ) < (β - 1) * realPartitionSeries β := by
      apply hres.eventually
      exact isOpen_Ioi.mem_nhds (by norm_num)
    have hsmall : ∀ᶠ β : ℝ in 𝓝[>] (1 : ℝ),
        β < 1 + 1 / (2 * b) := by
      have hshift : 1 < 1 + 1 / (2 * b) := by
        have hpos : 0 < 1 / (2 * b) := by positivity
        linarith
      apply (eventually_lt_nhds (a := (1 : ℝ))
        (b := 1 + 1 / (2 * b)) hshift).filter_mono
      exact nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hq, hsmall] with β hβ hqβ hsmallβ
    have hβ' : 1 < β := hβ
    have hδpos : 0 < β - 1 := by linarith
    have hδsmall : β - 1 < 1 / (2 * b) := by linarith
    have hδb : (β - 1) * b < (1 / 2 : ℝ) := by
      calc
        (β - 1) * b < (1 / (2 * b)) * b :=
          mul_lt_mul_of_pos_right hδsmall hbpos
        _ = (1 / 2 : ℝ) := by field_simp [ne_of_gt hbpos]
    have hz : b < realPartitionSeries β := by
      by_contra hnot
      have hzb : realPartitionSeries β ≤ b := le_of_not_gt hnot
      have hle := mul_le_mul_of_nonneg_left hzb (le_of_lt hδpos)
      linarith
    exact le_of_lt hz

end InfoGeometry.Arithmetic.ActualZetaPoleAsymptoticBridge
