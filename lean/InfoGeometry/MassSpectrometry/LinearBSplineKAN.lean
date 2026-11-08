/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.MassSpectrometry.CausalCrossGramian

/-!
# Continuous linear B-spline specialization for causal KAN kernels

The repository already contains an analytic complex-B-spline corridor in
features we additionally need a small real, compactly supported basis with
fully elementary proofs.

`linearBSpline c w` is the triangular degree-one B-spline

`max 0 (1 - |x-c| / w)`

for positive width `w`.  We prove continuity, nonnegativity, unit value at the
center, and compact support.  A finite family of these basis functions then
instantiates the existing `FiniteKANCausalKernel` interface.

No universal Kolmogorov-Arnold approximation theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open scoped BigOperators

/-- Compactly supported triangular degree-one B-spline. -/
def linearBSpline (center width x : ℝ) : ℝ :=
  max 0 (1 - |x - center| / width)

/-- Linear B-splines are nonnegative without any width hypothesis. -/
theorem linearBSpline_nonneg (center width x : ℝ) :
    0 ≤ linearBSpline center width x := by
  exact le_max_left _ _

/-- Positive-width linear B-splines attain value one at their center. -/
@[simp] theorem linearBSpline_at_center
    (center width : ℝ) :
    linearBSpline center width center = 1 := by
  simp [linearBSpline]

/-- Outside the closed width-radius support the linear B-spline vanishes. -/
theorem linearBSpline_eq_zero_of_width_le_abs
    {center width x : ℝ} (hwidth : 0 < width)
    (hout : width ≤ |x - center|) :
    linearBSpline center width x = 0 := by
  have hratio : 1 ≤ |x - center| / width := by
    apply (le_div_iff₀ hwidth).2
    simpa using hout
  have hnonpos : 1 - |x - center| / width ≤ 0 := sub_nonpos.mpr hratio
  simp [linearBSpline, max_eq_left hnonpos]

/-- The real triangular B-spline is continuous for every fixed center and
width. -/
theorem continuous_linearBSpline (center width : ℝ) :
    Continuous (linearBSpline center width) := by
  have habs : Continuous (fun x : ℝ => |x - center|) :=
    continuous_abs.comp (continuous_id.sub continuous_const)
  have hratio : Continuous (fun x : ℝ => |x - center| / width) :=
    habs.div_const width
  have hinterior : Continuous (fun x : ℝ => 1 - |x - center| / width) :=
    continuous_const.sub hratio
  change Continuous (fun x : ℝ => max 0 (1 - |x - center| / width))
  exact continuous_const.max hinterior

/-- Parameters for a finite B-spline KAN specialization. -/
structure LinearBSplineKANData (q : ℕ) where
  parentCenter : Fin q → ℝ
  parentWidth : Fin q → ℝ
  parentWidth_pos : ∀ k, 0 < parentWidth k
  parentScale : Fin q → ℝ
  childCenter : Fin q → ℝ
  childWidth : Fin q → ℝ
  childWidth_pos : ∀ k, 0 < childWidth k
  childScale : Fin q → ℝ
  outer : Fin q → ℝ → ℝ

namespace LinearBSplineKANData

/-- Parent inner coordinate for one KAN channel. -/
def parentInner {q : ℕ} (D : LinearBSplineKANData q)
    (k : Fin q) (x : ℝ) : ℝ :=
  D.parentScale k * linearBSpline (D.parentCenter k) (D.parentWidth k) x

/-- Child inner coordinate for one KAN channel. -/
def childInner {q : ℕ} (D : LinearBSplineKANData q)
    (k : Fin q) (x : ℝ) : ℝ :=
  D.childScale k * linearBSpline (D.childCenter k) (D.childWidth k) x

/-- Native specialization into the already-owned finite KAN causal kernel. -/
def toFiniteKANCausalKernel {q : ℕ} (D : LinearBSplineKANData q) :
    FiniteKANCausalKernel q where
  parentInner := D.parentInner
  childInner := D.childInner
  outer := D.outer

/-- Every parent B-spline inner channel is continuous. -/
theorem continuous_parentInner {q : ℕ} (D : LinearBSplineKANData q)
    (k : Fin q) : Continuous (D.parentInner k) := by
  exact continuous_const.mul
    (continuous_linearBSpline (D.parentCenter k) (D.parentWidth k))

/-- Every child B-spline inner channel is continuous. -/
theorem continuous_childInner {q : ℕ} (D : LinearBSplineKANData q)
    (k : Fin q) : Continuous (D.childInner k) := by
  exact continuous_const.mul
    (continuous_linearBSpline (D.childCenter k) (D.childWidth k))

/-- If every outer univariate channel is continuous, then the unmasked finite
B-spline KAN potential is jointly continuous in parent/child log mass. -/
theorem continuous_raw
    {q : ℕ} (D : LinearBSplineKANData q)
    (houter : ∀ k, Continuous (D.outer k)) :
    Continuous (fun p : ℝ × ℝ =>
      D.toFiniteKANCausalKernel.raw p.1 p.2) := by
  unfold FiniteKANCausalKernel.raw
  apply continuous_finset_sum
  intro k hk
  have hp : Continuous (fun p : ℝ × ℝ => D.parentInner k p.1) :=
    (D.continuous_parentInner k).comp continuous_fst
  have hc : Continuous (fun p : ℝ × ℝ => D.childInner k p.2) :=
    (D.continuous_childInner k).comp continuous_snd
  exact (houter k).comp (hp.add hc)

/-- The hard causal mask is continuous at every point strictly inside the
forward log-mass cone, where it agrees locally with the unmasked potential. -/
theorem continuousAt_causal_of_strict_cone
    {q : ℕ} (D : LinearBSplineKANData q)
    (houter : ∀ k, Continuous (D.outer k))
    {τParent τChild : ℝ} (hcone : τChild < τParent) :
    ContinuousAt
      (fun p : ℝ × ℝ =>
        D.toFiniteKANCausalKernel.causal p.1 p.2)
      (τParent, τChild) := by
  have hraw : Continuous
      (fun p : ℝ × ℝ =>
        D.toFiniteKANCausalKernel.raw p.1 p.2) :=
    D.continuous_raw houter
  have hopen : {p : ℝ × ℝ | p.2 < p.1} ∈ nhds (τParent, τChild) :=
    (isOpen_lt continuous_snd continuous_fst).mem_nhds hcone
  have heq :
      (fun p : ℝ × ℝ =>
        D.toFiniteKANCausalKernel.causal p.1 p.2) =ᶠ[nhds (τParent, τChild)]
      (fun p : ℝ × ℝ =>
        D.toFiniteKANCausalKernel.raw p.1 p.2) := by
    filter_upwards [hopen] with p hp
    simp [FiniteKANCausalKernel.causal, InForwardLogMassCone,
      le_of_lt hp]
  exact (hraw.continuousAt).congr heq.symm

/-- Strictly outside the forward log-mass cone, the hard causal mask is
locally zero and therefore continuous. -/
theorem continuousAt_causal_of_strictly_outside_cone
    {q : ℕ} (D : LinearBSplineKANData q)
    {τParent τChild : ℝ} (hout : τParent < τChild) :
    ContinuousAt
      (fun p : ℝ × ℝ =>
        D.toFiniteKANCausalKernel.causal p.1 p.2)
      (τParent, τChild) := by
  have hopen : {p : ℝ × ℝ | p.1 < p.2} ∈ nhds (τParent, τChild) :=
    (isOpen_lt continuous_fst continuous_snd).mem_nhds hout
  have heq :
      (fun p : ℝ × ℝ =>
        (0 : ℝ)) =ᶠ[nhds (τParent, τChild)]
      (fun p : ℝ × ℝ =>
        D.toFiniteKANCausalKernel.causal p.1 p.2) := by
    filter_upwards [hopen] with p hp
    simp [FiniteKANCausalKernel.causal, InForwardLogMassCone,
      not_le_of_gt hp]
  exact continuousAt_const.congr heq

/-- At a boundary point where the raw potential vanishes, the hard causal
mask is continuous.  The raw continuity hypothesis controls values on the
causal side, while the mask is exactly zero on the other side. -/
theorem continuousAt_causal_on_boundary_of_raw_eq_zero
    {q : ℕ} (D : LinearBSplineKANData q)
    (houter : ∀ k, Continuous (D.outer k))
    (τ : ℝ)
    (hzero : D.toFiniteKANCausalKernel.raw τ τ = 0) :
    ContinuousAt
      (fun p : ℝ × ℝ => D.toFiniteKANCausalKernel.causal p.1 p.2)
      (τ, τ) := by
  have hraw : ContinuousAt
      (fun p : ℝ × ℝ => D.toFiniteKANCausalKernel.raw p.1 p.2) (τ, τ) :=
    (D.continuous_raw houter).continuousAt
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hraw_eventually := (Metric.continuousAt_iff'.1 hraw) ε hε
  filter_upwards [hraw_eventually] with p hp
  have hp' :
      dist (D.toFiniteKANCausalKernel.raw p.1 p.2) 0 < ε := by
    simpa [hzero] using hp
  by_cases hcone : p.2 ≤ p.1
  · simpa [FiniteKANCausalKernel.causal, InForwardLogMassCone, hcone,
      hzero] using hp'
  · simpa [FiniteKANCausalKernel.causal, InForwardLogMassCone, hcone,
      hzero] using hε

/-- Continuity of the hard-masked kernel at a boundary point forces the raw
potential to vanish there.  The proof approaches from the strict exterior,
where the masked kernel is identically zero. -/
theorem raw_eq_zero_of_continuousAt_causal_on_boundary
    {q : ℕ} (D : LinearBSplineKANData q) (τ : ℝ)
    (hcont : ContinuousAt
      (fun p : ℝ × ℝ => D.toFiniteKANCausalKernel.causal p.1 p.2) (τ, τ)) :
    D.toFiniteKANCausalKernel.raw τ τ = 0 := by
  let x : ℕ → ℝ × ℝ := fun n =>
    (τ, τ + 1 / ((n : ℝ) + 1))
  let g : ℝ × ℝ → ℝ := fun p =>
    D.toFiniteKANCausalKernel.causal p.1 p.2
  have hx : Filter.Tendsto x Filter.atTop (nhds (τ, τ)) := by
    have hfirst :
        Filter.Tendsto (fun _ : ℕ => τ) Filter.atTop (nhds τ) :=
      tendsto_const_nhds
    have hdelta :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hsecond :
        Filter.Tendsto (fun n : ℕ => τ + 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds τ) := by
      simpa using hfirst.add hdelta
    simpa [x, nhds_prod_eq] using hfirst.prodMk hsecond
  have hlimit : Filter.Tendsto (g ∘ x) Filter.atTop (nhds (g (τ, τ))) := by
    exact hcont.tendsto.comp hx
  have hzero : ∀ n, g (x n) = 0 := by
    intro n
    apply FiniteKANCausalKernel.causal_eq_zero_of_not_cone
    dsimp [g, x, InForwardLogMassCone]
    apply not_le_of_gt
    apply lt_add_of_pos_right
    positivity
  have hlimit_zero : Filter.Tendsto (g ∘ x) Filter.atTop (nhds 0) := by
    have hfun : g ∘ x = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact hzero n
    rw [hfun]
    exact tendsto_const_nhds
  have hvalue : g (τ, τ) = 0 := tendsto_nhds_unique hlimit hlimit_zero
  simpa [g, FiniteKANCausalKernel.causal, InForwardLogMassCone] using hvalue

/-- At a boundary point, the hard-masked B-spline KAN potential is continuous
exactly when its raw value is zero, provided the raw potential is continuous. -/
theorem continuousAt_causal_on_boundary_iff_raw_eq_zero
    {q : ℕ} (D : LinearBSplineKANData q)
    (houter : ∀ k, Continuous (D.outer k)) (τ : ℝ) :
    ContinuousAt
        (fun p : ℝ × ℝ => D.toFiniteKANCausalKernel.causal p.1 p.2)
        (τ, τ) ↔
      D.toFiniteKANCausalKernel.raw τ τ = 0 := by
  constructor
  · exact D.raw_eq_zero_of_continuousAt_causal_on_boundary τ
  · exact D.continuousAt_causal_on_boundary_of_raw_eq_zero houter τ

/-- Parent channel support is compact in the elementary sense that the channel
vanishes once the center-distance is at least its positive width. -/
theorem parentInner_eq_zero_of_outside
    {q : ℕ} (D : LinearBSplineKANData q) (k : Fin q) {x : ℝ}
    (hout : D.parentWidth k ≤ |x - D.parentCenter k|) :
    D.parentInner k x = 0 := by
  simp [parentInner,
    linearBSpline_eq_zero_of_width_le_abs (D.parentWidth_pos k) hout]

/-- Child channel support is compact in the same sense. -/
theorem childInner_eq_zero_of_outside
    {q : ℕ} (D : LinearBSplineKANData q) (k : Fin q) {x : ℝ}
    (hout : D.childWidth k ≤ |x - D.childCenter k|) :
    D.childInner k x = 0 := by
  simp [childInner,
    linearBSpline_eq_zero_of_width_le_abs (D.childWidth_pos k) hout]

/-- The B-spline specialization inherits the hard causal-cone support theorem. -/
theorem cone_of_causal_ne_zero
    {q : ℕ} (D : LinearBSplineKANData q)
    {τParent τChild : ℝ}
    (h : D.toFiniteKANCausalKernel.causal τParent τChild ≠ 0) :
    InForwardLogMassCone τParent τChild := by
  exact FiniteKANCausalKernel.cone_of_causal_ne_zero
    D.toFiniteKANCausalKernel h

end LinearBSplineKANData

end InfoGeometry.MassSpectrometry
