/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# InfoGeometry.Analysis.MellinGaussianHolomorphicWeighted

Ported to Mathlib `v4.34.1` from `mccorvie/riemann-masullo` (Apache-2.0, upstream
commit `b967ac4`):
- `RiemannMasullo/ForMathlib/Analysis/MellinTransform/Gaussian.lean`
- `RiemannMasullo/ForMathlib/Analysis/MellinTransform/Holomorphic.lean`
- `RiemannMasullo/ForMathlib/Analysis/MellinTransform/Weighted.lean`

Provides:
- `mellin_gaussian`: `mellin (fun t : ℝ ↦ (Real.exp (-a * t ^ 2) : ℂ)) z =
  (2 : ℂ)⁻¹ * ((a : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2))`;
- `integral_comp_abs_complex` and `integral_radial`;
- `analyticOnNhd_integral_mul_cpow_of_integrable` and `analyticOnNhd_integral_mul_cpow`;
- `tendstoUniformlyOn_mellinBands`.
-/

noncomputable section

open Filter MeasureTheory Set Metric
open scoped Topology

namespace InfoGeometry.Analysis.MellinGaussianHolomorphicWeighted

/-- The Mellin transform of a Gaussian on the positive real ray. -/
theorem mellin_gaussian {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    mellin (fun t : ℝ ↦ (Real.exp (-a * t ^ 2) : ℂ)) z =
      (2 : ℂ)⁻¹ * ((a : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2)) := by
  let f (t : ℝ) : ℂ := Real.exp (-t)
  have he : (fun t : ℝ ↦ (Real.exp (-a * t ^ 2) : ℂ)) = fun t : ℝ ↦ f (a * t ^ (2 : ℝ)) := by
    funext t
    simp [f]
  rw [he, mellin_comp_rpow (fun r ↦ f (a * r)) z 2, mellin_comp_mul_left f _ ha,
    Complex.Gamma_eq_integral (s := z / 2) (by simpa using hz), Complex.GammaIntegral_eq_mellin]
  simp [f, Complex.real_smul]

/-- Integration of an even complex function on the real line reduces to its positive ray. -/
theorem integral_comp_abs_complex (f : ℝ → ℂ) :
    (∫ x : ℝ, f |x|) = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  let g (x : ℝ) := f |x|
  have hpos : (∫ x in Ioi (0 : ℝ), g x) = ∫ x in Ioi (0 : ℝ), f x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ congrArg f (abs_of_pos hx)
  have hneg : (∫ x in Iic (0 : ℝ), g x) = ∫ x in Ioi (0 : ℝ), g x := by
    simpa only [g, neg_zero, abs_neg] using (integral_comp_neg_Ioi 0 g).symm
  by_cases hg : Integrable g
  · have hu := setIntegral_union (f := g) (Iic_disjoint_Ioi (a := (0 : ℝ)) le_rfl) measurableSet_Ioi
        hg.integrableOn hg.integrableOn
    rw [Iic_union_Ioi, setIntegral_univ, hneg, hpos, ← two_mul] at hu
    exact hu
  · have h : ¬ IntegrableOn g (Ioi 0) := by
      intro h
      apply hg
      have h' : IntegrableOn g (Iic 0) := by
        have m : MeasurableEmbedding (fun x : ℝ ↦ -x) := (Homeomorph.neg ℝ).measurableEmbedding
        rw [← Measure.map_neg_eq_self (volume : Measure ℝ), m.integrableOn_map_iff]
        simpa [g, Function.comp_def, neg_preimage, neg_Iic,
          integrableOn_Ici_iff_integrableOn_Ioi] using h
      simpa [Iic_union_Ioi] using h'.union h
    rw [← hpos, integral_undef hg, integral_undef h, mul_zero]

/-- Polar integration of a complex-valued function of the radius. -/
theorem integral_radial (f : ℝ → ℂ) :
    (∫ z : ℂ, f ‖z‖) = (2 * (Real.pi : ℂ)) * ∫ r in Ioi (0 : ℝ), (r : ℂ) * f r := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  calc
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ((p.1 : ℂ) * f p.1) * 1 := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, Complex.real_smul, mul_one]
    _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * f r) * ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
      rw [← setIntegral_prod_mul, Measure.volume_eq_prod]
    _ = _ := by
      rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
        Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), Complex.real_smul, mul_one]
      push_cast
      ring

/-- Integrating a complex power of a positive measurable function against a fixed weight
is holomorphic in every open strip in which the weighted integrand is integrable. -/
theorem analyticOnNhd_integral_mul_cpow_of_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℂ) (n : α → ℝ) (hn : Measurable n) (hp : ∀ x, 0 < n x)
    {I : Set ℝ} (hI : IsOpen I)
    (hint : ∀ z : ℂ, z.re ∈ I → Integrable (fun x ↦ f x * (n x : ℂ) ^ z) μ) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ x, f x * (n x : ℂ) ^ z ∂μ) (Complex.re ⁻¹' I) := by
  let W (z : ℂ) (x : α) := f x * (n x : ℂ) ^ z
  let D (z : ℂ) (x : α) := W z x * Complex.log (n x : ℂ)
  have hD (z : ℂ) (x : α) : HasDerivAt (fun w ↦ W w x) (D z x) z := by
    simpa only [W, D, id_eq, mul_assoc, mul_one] using
      (((hasDerivAt_id z).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (hp x).ne'))).const_mul
        (f x))
  apply DifferentiableOn.analyticOnNhd _ (hI.preimage Complex.continuous_re)
  intro z hz
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hz)
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let a := z.re - 2 * r
  let b := z.re + 2 * r
  have ha : a ∈ I := hsub (by rw [mem_ball, Real.dist_eq, abs_lt]; dsimp [a, r]; constructor <;> linarith)
  have hb : b ∈ I := hsub (by rw [mem_ball, Real.dist_eq, abs_lt]; dsimp [b, r]; constructor <;> linarith)
  have hnorm (w : ℂ) (x : α) : ‖W w x‖ = ‖f x‖ * n x ^ w.re := by
    dsimp only [W]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hp x)]
  have hbound (x : α) (w : ℂ) (hw : w ∈ ball z r) :
      ‖D w x‖ ≤ (‖W a x‖ + ‖W b x‖) / r := by
    rw [← (hD w x).deriv]
    have hdiff : Differentiable ℂ (fun t ↦ W t x) := fun t ↦ (hD t x).differentiableAt
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff.diffContOnCl
    intro t ht
    have hd : |t.re - z.re| ≤ 2 * r := calc
      |t.re - z.re| ≤ dist t z := by
        simpa only [dist_eq_norm, Complex.sub_re] using Complex.abs_re_le_norm (t - z)
      _ ≤ dist t w + dist w z := dist_triangle _ _ _
      _ ≤ 2 * r := by rw [mem_sphere.mp ht]; linarith [mem_ball.mp hw]
    rw [hnorm, hnorm, hnorm, Complex.ofReal_re, Complex.ofReal_re]
    rcases le_total 1 (n x) with h | h
    · exact le_add_of_nonneg_of_le (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hp x).le _))
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le h (by dsimp [b]; linarith [(abs_le.mp hd).2]))
          (norm_nonneg _))
    · exact le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hp x) h (by dsimp [a]; linarith [(abs_le.mp hd).1]))
        (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hp x).le _))
  have hmeas : ∀ᶠ t : ℂ in 𝓝 z, AEStronglyMeasurable (W t) μ :=
    Filter.Eventually.mono ((hI.preimage Complex.continuous_re).mem_nhds hz) fun t ht ↦
      (hint t ht).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z hr) hmeas (hint z hz)
    ((hint z hz).aestronglyMeasurable.mul
      ((Complex.measurable_log.comp (Complex.continuous_ofReal.measurable.comp hn)).aestronglyMeasurable))
    (ae_of_all _ hbound) (((hint a ha).norm.add (hint b hb).norm).div_const r)
    (ae_of_all _ fun x w _ ↦ hD w x)).2.differentiableAt.differentiableWithinAt

/-- A weighted Mellin integral is holomorphic on any open strip on which it
converges absolutely. The two nearby real powers dominate its logarithmic derivative. -/
theorem analyticOnNhd_integral_mul_cpow {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℂ) (r : X → ℝ) (hf : Measurable f) (hr : Measurable r) (hp : ∀ x, 0 < r x)
    {U : Set ℝ} (ho : IsOpen U) (hi : ∀ a ∈ U, Integrable (fun x ↦ ‖f x‖ * r x ^ a) μ) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ ∫ x, f x * (r x : ℂ) ^ s ∂μ) (Complex.re ⁻¹' U) := by
  apply DifferentiableOn.analyticOnNhd _ (ho.preimage Complex.continuous_re)
  intro s hs
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hs)
  let ε := δ / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  let lo := s.re - 2 * ε
  let up := s.re + 2 * ε
  have h2 : 2 * ε < δ := by dsimp [ε]; linarith
  have hl : lo ∈ U := hd (by
    rw [Metric.mem_ball, Real.dist_eq]
    change |s.re - 2 * ε - s.re| < δ
    rw [show s.re - 2 * ε - s.re = -(2 * ε) by ring, abs_neg, abs_of_pos (by positivity)]
    exact h2)
  have hu : up ∈ U := hd (by
    rw [Metric.mem_ball, Real.dist_eq]
    change |s.re + 2 * ε - s.re| < δ
    rwa [add_sub_cancel_left, abs_of_pos (by positivity)])
  let W (z : ℂ) (x : X) := f x * (r x : ℂ) ^ z
  let D (z : ℂ) (x : X) := W z x * Complex.log (r x : ℂ)
  have hW (z : ℂ) : Measurable (W z) := hf.mul (hr.complex_ofReal.pow_const _)
  have hN (z : ℂ) (x : X) : ‖W z x‖ = ‖f x‖ * r x ^ z.re := by
    dsimp only [W]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hp x)]
  let M (x : X) := (‖f x‖ * r x ^ lo + ‖f x‖ * r x ^ up) * ε⁻¹
  have hM : Integrable M μ := ((hi lo hl).add (hi up hu)).mul_const _
  have hbound (x : X) (z : ℂ) (hz : z ∈ Metric.ball s ε) : ‖D z x‖ ≤ M x := by
    have hz' : |z.re - s.re| < ε := (Complex.abs_re_le_norm (z - s)).trans_lt
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
    have hlog : ‖Complex.log (r x : ℂ)‖ = |Real.log (r x)| := by
      rw [← Complex.ofReal_log (hp x).le, Complex.norm_real, Real.norm_eq_abs]
    dsimp only [D, M]
    rw [norm_mul, hN, hlog, ← div_eq_mul_inv]
    apply (le_div_iff₀ hε).2
    let t := Real.log (r x)
    have he : |t| * ε ≤ Real.exp (ε * |t|) := by
      rw [mul_comm]
      linarith [Real.add_one_le_exp (ε * |t|)]
    have hpow (a : ℝ) : r x ^ a = Real.exp (t * a) := Real.rpow_def_of_pos (hp x) a
    have hrange := abs_lt.mp hz'
    rcases le_total 0 t with ht | ht
    · apply le_add_of_nonneg_of_le (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hp x).le _))
      rw [hpow, hpow]
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ Real.exp (t * z.re) * Real.exp (ε * |t|) := mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)
        _ ≤ _ := by
          rw [← Real.exp_add, Real.exp_le_exp, abs_of_nonneg ht]
          dsimp [up]
          nlinarith [mul_nonneg ht (show 0 ≤ s.re + ε - z.re by linarith [hrange.2])]
    · apply le_add_of_le_of_nonneg _ (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hp x).le _))
      rw [hpow, hpow]
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ Real.exp (t * z.re) * Real.exp (ε * |t|) := mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)
        _ ≤ _ := by
          rw [← Real.exp_add, Real.exp_le_exp, abs_of_nonpos ht]
          dsimp [lo]
          nlinarith [mul_nonpos_of_nonpos_of_nonneg ht (show 0 ≤ z.re - s.re + ε by linarith [hrange.1])]
  have hder (x : X) (z : ℂ) : HasDerivAt (fun w ↦ W w x) (D z x) z := by
    simpa only [W, D, id_eq, mul_assoc, mul_one] using
      (((hasDerivAt_id z).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (hp x).ne'))).const_mul (f x))
  have hI : Integrable (W s) μ :=
    (hi s.re hs).mono' (hW s).aestronglyMeasurable (.of_forall fun x ↦ (hN s x).le)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds _ hε)
    (.of_forall fun z ↦ (hW z).aestronglyMeasurable) hI
    ((hW s).mul (Complex.measurable_log.comp hr.complex_ofReal)).aestronglyMeasurable
    (.of_forall hbound) hM (.of_forall fun x z _ ↦ hder x z)).2.differentiableAt.differentiableWithinAt

/-- An integrable Mellin family is uniformly approximated by norm bands when
the abscissa ranges over a compact set. Its two endpoint integrands dominate
the two tails on opposite sides of norm one. -/
theorem tendstoUniformlyOn_mellinBands {X P : Type*} [MeasurableSpace X]
    [TopologicalSpace P] (μ : Measure X) (r : X → ℝ) (hr : ∀ x, 0 < r x) (hm : Measurable r)
    (A : X → ℝ) (hA : ∀ x, 0 ≤ A x) (σ : P → ℝ) (H : P → X → ℂ)
    (K : Set P) (hK : IsCompact K) (hσ : ContinuousOn σ K)
    (hI : ∀ p ∈ K, Integrable (H p) μ)
    (hN : ∀ p ∈ K, ∀ x, ‖H p x‖ = A x * r x ^ σ p) :
    TendstoUniformlyOn (fun (n : ℕ) p ↦ ∫ x in {x | r x ∈ Icc (n + 1 : ℝ)⁻¹ (n + 1)}, H p x ∂μ)
      (fun p ↦ ∫ x, H p x ∂μ) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hσ
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hσ
  let M (x : X) := ‖H a x‖ + ‖H b x‖
  have hM : Integrable M μ := (hI a ha).norm.add (hI b hb).norm
  have hle {p : P} (hp : p ∈ K) (x : X) : ‖H p x‖ ≤ M x := by
    dsimp only [M]
    rcases le_total (r x) 1 with hx | hx
    · apply le_add_of_le_of_nonneg _ (norm_nonneg _)
      rw [hN p hp, hN a ha]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hr x) hx (hmin hp)) (hA x)
    · apply le_add_of_nonneg_of_le (norm_nonneg _) _
      rw [hN p hp, hN b hb]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (hmax hp)) (hA x)
  let B (n : ℕ) := {x | r x ∈ Icc (n + 1 : ℝ)⁻¹ (n + 1)}
  have hB (n : ℕ) : MeasurableSet (B n) := hm measurableSet_Icc
  have hmono : Monotone B := by
    intro i j hij x hx
    have h : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.succ_le_succ hij
    exact ⟨((inv_le_inv₀ (by positivity) (by positivity)).mpr h).trans hx.1, hx.2.trans h⟩
  have hexhaust : (⋂ n, (B n)ᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max (r x) (r x)⁻¹)
    have h : max (r x) (r x)⁻¹ ≤ (n : ℝ) + 1 := hn.le.trans (by linarith)
    exact (mem_iInter.mp hx n) ⟨(inv_le_comm₀ (by positivity) (hr x)).2 ((le_max_right _ _).trans h),
      (le_max_left _ _).trans h⟩
  have hlim : Tendsto (fun n ↦ ∫ x in (B n)ᶜ, M x ∂μ) atTop (𝓝 0) := by
    simpa only [hexhaust, setIntegral_empty] using
      (tendsto_setIntegral_of_antitone (μ := μ) (f := M) (fun n ↦ (hB n).compl)
        (fun _ _ hij ↦ compl_subset_compl.mpr (hmono hij)) ⟨0, hM.integrableOn⟩)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn p hp
  change dist (∫ x, H p x ∂μ) (∫ x in B n, H p x ∂μ) < ε
  rw [dist_eq_norm, ← integral_add_compl (hB n) (hI p hp), add_sub_cancel_left]
  exact (norm_integral_le_integral_norm _).trans_lt ((setIntegral_mono_on
    (hI p hp).norm.integrableOn hM.integrableOn (hB n).compl (fun x _ ↦ hle hp x)).trans_lt hn)

end InfoGeometry.Analysis.MellinGaussianHolomorphicWeighted
