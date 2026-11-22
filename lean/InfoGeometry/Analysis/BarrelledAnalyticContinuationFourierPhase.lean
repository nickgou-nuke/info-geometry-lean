/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# InfoGeometry.Analysis.BarrelledAnalyticContinuationFourierPhase

Ported to Mathlib `v4.34.1` from `mccorvie/riemann-masullo` (Apache-2.0, upstream
commit `b967ac4`):
- `RiemannMasullo/ForMathlib/Analysis/LocallyConvex/Barrelled.lean`
- `RiemannMasullo/ForMathlib/Analysis/Fourier/FourierPhase.lean`

Provides:
- `exists_continuousLinearMap_of_analytic_continuation`: analytic continuation of
  continuity along connected open sets in barrelled spaces;
- `continuous_of_continuous_eval_barrelled`: Banach–Steinhaus continuity into `C(X, ℂ)`;
- `exists_continuousLinearMap_integral_mul`: continuous linear functionals via
  pointwise bounded families integrated against continuous weights;
- `hasDerivAt_integral_fourier_phase`: differentiation under the integral sign
  for finite sums of real Fourier phases dominated by first absolute moments.
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace InfoGeometry.Analysis.BarrelledAnalyticContinuationFourierPhase

/-- A pointwise holomorphic family of functionals on a barrelled space consists of continuous
linear functionals throughout a connected open set if it does so in a neighborhood of one point. -/
theorem exists_continuousLinearMap_of_analytic_continuation
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (Φ : E → ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hΦ : ∀ f, AnalyticOnNhd ℂ (Φ f) U)
    {b : ℂ} (hb : b ∈ U) (hbase : ∀ᶠ z in 𝓝 b, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z)
    {z : ℂ} (hz : z ∈ U) : ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z := by
  classical
  let P := {z : ℂ | ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z}
  let V := interior P ∩ U
  have hV : IsOpen V := isOpen_interior.inter hU
  have analyticDeriv (f : E) {x : ℂ} (hx : x ∈ U) (n : ℕ) : AnalyticAt ℂ (iteratedDeriv n (Φ f)) x := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hΦ f x hx
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hcoeff (n : ℕ) : ∀ y ∈ V, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = iteratedDeriv n (Φ f) y := by
    induction n with
    | zero => exact fun y hy ↦ by simp only [iteratedDeriv_zero]; exact (interior_subset hy.1 : y ∈ P)
    | succ n ih =>
      intro x hx
      let A (y : ℂ) : E →L[ℂ] ℂ := if hy : y ∈ V then (ih y hy).choose else 0
      have hA {y : ℂ} (hy : y ∈ V) (f : E) : A y f = iteratedDeriv n (Φ f) y := by
        simpa only [A, dite_eq_left hy] using (ih y hy).choose_spec f
      let D (y : ℂ) := (y - x)⁻¹ • (A y - A x)
      have hlim : Tendsto (fun y f ↦ D y f) (𝓝[≠] x) (𝓝 fun f ↦ iteratedDeriv (n + 1) (Φ f) x) := by
        refine tendsto_pi_nhds.mpr fun f ↦ ?_
        have hd := analyticDeriv f hx.2 n
        rw [iteratedDeriv_succ]
        refine hd.differentiableAt.hasDerivAt.tendsto_slope.congr' ?_
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hx)] with y hy
        simp only [D, smul_apply, sub_apply, hA hy, hA hx, slope, vsub_eq_sub]
      exact ⟨continuousLinearMapOfTendsto D hlim, fun _ ↦ rfl⟩
  have hball (y : ℂ) (hy : y ∈ V) {r : ℝ} (hr : Metric.ball y r ⊆ U) : Metric.ball y r ⊆ P := by
    choose A hA using fun n ↦ hcoeff n y hy
    intro x hx
    let T (s : Finset ℕ) : E →L[ℂ] ℂ := ∑ n ∈ s, (n.factorial : ℂ)⁻¹ • (x - y) ^ n • A n
    have hlim : Tendsto (fun s f ↦ T s f) atTop (𝓝 fun f ↦ Φ f x) := by
      refine tendsto_pi_nhds.mpr fun f ↦ ?_
      have h := Complex.hasSum_taylorSeries_on_ball ((hΦ f).differentiableOn.mono hr) hx
      simp only [T, sum_apply, smul_apply, hA]
      exact h
    exact ⟨continuousLinearMapOfTendsto T hlim, fun _ ↦ rfl⟩
  apply interior_subset (s := P)
  suffices h : U ⊆ V from (h hz).1
  refine hconn.subset_of_closure_inter_subset hV ⟨b, hb, mem_interior_iff_mem_nhds.mpr hbase, hb⟩ ?_
  rintro x ⟨hx, hxU⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (r / 2) (half_pos hr)
  have hballU : Metric.ball y (r / 2) ⊆ U := (Metric.ball_subset_ball' (by
    rw [dist_comm y x]; linarith : r / 2 + dist y x ≤ r)).trans hsub
  exact ⟨interior_maximal (hball y hy hballU) Metric.isOpen_ball hxy, hxU⟩

/-- For linear maps from a barrelled space into continuous functions with the compact-open
topology, continuity of all point evaluations implies continuity of the map. -/
theorem continuous_of_continuous_eval_barrelled
    {E X : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] [TopologicalSpace X] (T : E → C(X, ℂ))
    (heval : ∀ x, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = T f x) : Continuous T := by
  choose L hL using heval
  refine continuous_iff_continuousAt.mpr fun f ↦ ?_
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A (x : K) := L x.val
  have hbound (g : E) : Bornology.IsVonNBounded ℂ (range fun x : K ↦ A x g) := by
    have hc : Continuous (fun x : K ↦ T g x.val) := (T g).continuous.comp continuous_subtype_val
    simpa only [A, hL] using (isCompact_range hc).isVonNBounded ℂ
  have he := (PolynormableSpace.banach_steinhaus hbound).equicontinuous f
  intro u hu
  filter_upwards [he u hu] with g hg
  intro x hx
  simpa only [Function.comp_apply, A, hL] using hg (⟨x, hx⟩ : K)

/-- Integrating a pointwise bounded family of continuous linear forms against a
continuous weight gives a continuous linear form whenever each integral converges.
On compact subsets the supremum of the evaluation seminorms bounds the integral.
Banach–Steinhaus then gives continuity of the limit along a compact exhaustion. -/
theorem exists_continuousLinearMap_integral_mul {E X : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (v : X → E →ₗ[ℂ] ℂ)
    (hv : ∀ x, Continuous (fun e ↦ ‖v x e‖)) (hb : ∀ e, ∃ B : ℝ, ∀ x, ‖v x e‖ ≤ B)
    (w : X → ℂ) (hw : Continuous w) (hi : ∀ e, Integrable (fun x ↦ v x e * w x) μ) :
    ∃ Z : E →L[ℂ] ℂ, ∀ e, Z e = ∫ x, v x e * w x ∂μ := by
  let q (x : X) := (normSeminorm ℂ ℂ).comp (v x)
  have hq : BddAbove (range q) := Seminorm.bddAbove_range_iff.mpr fun e ↦ by
    obtain ⟨B, hB⟩ := hb e
    exact ⟨B, forall_mem_range.mpr hB⟩
  let p : Seminorm ℂ E := ⨆ x, q x
  have hp : Continuous p := by
    rw [show (p : E → ℝ) = ⨆ x, (q x : E → ℝ) from Seminorm.coe_iSup_eq hq]
    exact Seminorm.continuous_iSup q hv hq
  have hle (e : E) (x : X) : ‖v x e‖ ≤ p e := (le_ciSup hq x : q x ≤ p) e
  let K := compactCovering X
  have hK (n : ℕ) : IsCompact (K n) := isCompact_compactCovering X n
  let L (n : ℕ) : E →ₗ[ℂ] ℂ :=
    { toFun := fun e ↦ ∫ x in K n, v x e * w x ∂μ
      map_add' := fun a b ↦ by
        simp_rw [map_add, add_mul]
        exact integral_add (hi a).integrableOn (hi b).integrableOn
      map_smul' := fun z e ↦ by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_assoc, integral_const_mul] }
  have hc (n : ℕ) : Continuous (L n) := by
    let B := ∫ x in K n, ‖w x‖ ∂μ
    let b : ℝ≥0 := ⟨B, integral_nonneg fun _ ↦ norm_nonneg _⟩
    apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp (L n)
    intro _
    apply Seminorm.continuous_of_le (q := b • p) (hp.const_smul b)
    intro e
    change ‖∫ x in K n, v x e * w x ∂μ‖ ≤ B * p e
    rw [mul_comm B, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
      (hi e).norm.integrableOn ((hw.norm.continuousOn.integrableOn_compact (hK n)).const_mul _)
      (hK n).measurableSet fun x _ ↦ ?_)
    exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hle e x) (norm_nonneg _))
  let T (n : ℕ) : E →L[ℂ] ℂ := ⟨L n, hc n⟩
  have hlim : Tendsto (fun n e ↦ T n e) atTop (𝓝 (fun e ↦ ∫ x, v x e * w x ∂μ)) := by
    apply tendsto_pi_nhds.mpr
    intro e
    change Tendsto (fun n ↦ ∫ x in K n, v x e * w x ∂μ) atTop (𝓝 _)
    simpa only [K, iUnion_compactCovering, setIntegral_univ] using
      (tendsto_setIntegral_of_monotone (fun n ↦ (hK n).measurableSet)
        (fun _ _ h ↦ compactCovering_subset X h) (hi e).integrableOn)
  exact ⟨continuousLinearMapOfTendsto T hlim, fun _ ↦ rfl⟩

/-- First absolute moments dominate the derivative of a finite sum of real Fourier phases. -/
theorem hasDerivAt_integral_fourier_phase {Y ι : Type*} [MeasurableSpace Y] [Fintype ι]
    (μ : Measure Y) (a : Y → ℂ) (ha : Integrable a μ) (k : ι → Y → ℂ)
    (hk : ∀ i, AEStronglyMeasurable (k i) μ)
    (hm : ∀ i, Integrable (fun y ↦ ‖a y‖ * ‖k i y‖) μ)
    (z dz : ℝ → ι → ℂ) (hz : ∀ s i, HasDerivAt (fun t ↦ z t i) (dz s i) s)
    (hz0 : ∀ i, z 0 i = 0) (hd : ∀ i, Continuous fun s ↦ dz s i) :
    let P (s : ℝ) (y : Y) := 2 * Real.pi * ∑ i, (z s i * k i y).re
    let D (y : Y) := a y * (((2 * Real.pi * ∑ i, (dz 0 i * k i y).re : ℝ) : ℂ) * Complex.I)
    Integrable D μ ∧ HasDerivAt (fun s ↦ ∫ y, a y * (Circle.exp (P s y) : ℂ) ∂μ)
      (∫ y, D y ∂μ) 0 := by
  classical
  let P (u : ι → ℂ) (y : Y) := 2 * Real.pi * ∑ i, (u i * k i y).re
  let K (s : ℝ) (y : Y) : ℂ := Circle.exp (P (z s) y)
  let D (s : ℝ) (y : Y) := a y * (K s y * ((P (dz s) y : ℂ) * Complex.I))
  have hP (u : ι → ℂ) : AEStronglyMeasurable (P u) μ := by
    apply AEStronglyMeasurable.const_mul
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
      Complex.continuous_re.comp_aestronglyMeasurable ((hk i).const_mul _)
  have hK (s) : AEStronglyMeasurable (K s) μ :=
    (show Continuous (fun x : ℝ ↦ (Circle.exp x : ℂ)) from
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).comp_aestronglyMeasurable
        (hP _)
  have hder (s : ℝ) (y : Y) : HasDerivAt (fun t ↦ a y * K t y) (D s y) s := by
    have h : HasDerivAt (fun t ↦ P (z t) y) (P (dz s) y) s :=
      (HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt s ((hz s i).mul_const (k i y))).const_mul _
    exact ((h.ofReal_comp.mul_const Complex.I).cexp).const_mul (a y)
  choose C hC using fun i ↦ isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) (hd i).continuousOn
  let bound (y : Y) := (2 * Real.pi) * ∑ i, C i * (‖a y‖ * ‖k i y‖)
  have hbound : Integrable bound μ :=
    (integrable_finsetSum _ fun i _ ↦ (hm i).const_mul (C i)).const_mul _
  have hle (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) (y : Y) : ‖D s y‖ ≤ bound y := by
    have hreal : ‖∑ i, (dz s i * k i y).re‖ ≤ ∑ i, C i * ‖k i y‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum fun i _ ↦ (Complex.abs_re_le_norm _).trans
        ((norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hC i s hs) (norm_nonneg _)))
    have hnonneg : 0 ≤ 2 * Real.pi := by positivity
    change ‖a y * (K s y * ((P (dz s) y : ℂ) * Complex.I))‖ ≤ _
    simp only [norm_mul, K, Circle.norm_coe, Complex.norm_I, mul_one, one_mul,
      Complex.norm_real, P, Real.norm_of_nonneg hnonneg]
    calc
      _ ≤ ‖a y‖ * ((2 * Real.pi) * ∑ i, C i * ‖k i y‖) := by gcongr
      _ = bound y := by
        simp only [bound, ← mul_assoc, Finset.mul_sum]
        ring_nf
  have hK0 (y : Y) : K 0 y = 1 := by simp [K, P, hz0]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun s y ↦ a y * K s y)
    (F' := D) (s := Icc (-1 : ℝ) 1) (Icc_mem_nhds (by norm_num) (by norm_num))
    (.of_forall fun s ↦ ha.1.mul (hK s)) (by simpa only [hK0, mul_one] using ha)
    (ha.1.mul ((hK 0).mul ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hP _)).mul_const _)))
    (.of_forall fun y s hs ↦ hle s hs y) hbound (.of_forall fun y s _ ↦ hder s y)
  simpa only [D, hK0, one_mul] using h

end InfoGeometry.Analysis.BarrelledAnalyticContinuationFourierPhase
