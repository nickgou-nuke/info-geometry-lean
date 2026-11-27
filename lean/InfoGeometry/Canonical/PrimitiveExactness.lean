/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZeroHolonomyAnalyticity

/-!
# Primitive exactness bridge

This file records the theorem-safe part of the primitive-exactness story.

Mathlib's primitive API is `Complex.IsExactOn f U`, meaning that `f` is the
complex derivative of a primitive on `U`.  The current Mathlib theorem available
without extra topological machinery is disk-local:

* `DifferentiableOn.isExactOn_ball`

We therefore prove only the disk-local and explicitly-premised consequences.
There is no postulate for a global partition function and no claim that an
arbitrary global domain is simply connected.

#### BUCKET 1: CLOSED FINITE THEOREMS
None.  This file is analytic and conditional on Mathlib hypotheses.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
Holomorphicity on a disk gives `Complex.IsExactOn`; primitive exactness on an
open set gives zero rectangular holonomy and the repo Cauchy/Hestenes analytic
readbacks.

#### BUCKET 3: OPEN CLOSURE DEBT
No global zeta/xi primitive, arbitrary Wilson-loop theorem, or simply-connected
domain primitive theorem is claimed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimitiveExactness

open Complex
open InfoGeometry.Canonical.ComplexAnalyticBridge
open InfoGeometry.Canonical.ZeroHolonomyAnalyticity
open InfoGeometry.Geometry.BilingualAnalyticity

open scoped Topology

/--
Mathlib's disk-local primitive theorem: a holomorphic function on a ball has a
primitive on that ball.
-/
theorem differentiableOn_ball_to_isExactOn
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    IsExactOn f (Metric.ball c r) :=
  hf.isExactOn_ball

/--
Unfolded primitive witness form of `differentiableOn_ball_to_isExactOn`.
-/
theorem differentiableOn_ball_exists_primitive
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∃ F : ℂ → ℂ, ∀ z ∈ Metric.ball c r, HasDerivAt F (f z) z :=
  differentiableOn_ball_to_isExactOn hf

/--
Primitive exactness on an open set implies zero rectangular holonomy.

This is the exact Mathlib/repo translation: `IsExactOn` gives
`DifferentiableOn`, differentiability gives Mathlib conservativity, and
conservativity is the zero-rectangle-holonomy condition used in
`ZeroHolonomyAnalyticity`.
-/
theorem primitiveExactOn_to_zeroRectangularHolonomyOn
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hExact : IsExactOn f U) :
    ZeroRectangularHolonomyOn f U :=
  zeroRectangularHolonomyOn_of_isExactOn hU hExact

/--
Holomorphicity on a disk implies zero rectangular holonomy on that disk.
-/
theorem differentiableOn_ball_to_zeroRectangularHolonomyOn
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ZeroRectangularHolonomyOn f (Metric.ball c r) :=
  primitiveExactOn_to_zeroRectangularHolonomyOn
    Metric.isOpen_ball (differentiableOn_ball_to_isExactOn hf)

/--
Primitive exactness on an open set gives Mathlib pointwise analyticity.
-/
theorem primitiveExactOn_to_analyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : IsExactOn f U) :
    AnalyticAt ℂ f z :=
  isExactOn_to_analyticAt hU hz hExact

/--
Primitive exactness on an open set gives the repo Cauchy/Hestenes pointwise
analyticity readback.
-/
def primitiveExactOn_to_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : IsExactOn f U) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  isExactOn_to_cauchyAnalyticAt hU hz hExact

/--
Holomorphicity on a disk gives the repo Cauchy/Hestenes pointwise analyticity
readback at any point of the disk.
-/
def differentiableOn_ball_to_cauchyAnalyticAt
    {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hz : z ∈ Metric.ball c r) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  primitiveExactOn_to_cauchyAnalyticAt
    Metric.isOpen_ball hz (differentiableOn_ball_to_isExactOn hf)

/--
Primitive exactness on an open set transports to the doubled/clock-axis
pointwise analyticity structure.
-/
def primitiveExactOn_to_doubled_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : IsExactOn f U) :
    CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
      (lifted f) (complexToDoubled z) :=
  isExactOn_to_doubled_cauchyAnalyticAt hU hz hExact

/--
Holomorphicity on a disk transports to the doubled/clock-axis pointwise
analyticity structure.
-/
def differentiableOn_ball_to_doubled_cauchyAnalyticAt
    {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hz : z ∈ Metric.ball c r) :
    CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
      (lifted f) (complexToDoubled z) :=
  primitiveExactOn_to_doubled_cauchyAnalyticAt
    Metric.isOpen_ball hz (differentiableOn_ball_to_isExactOn hf)

/-! ## Group A: Convex domain primitive exactness (`Convex ℝ U`) -/

/--
A holomorphic function on an open convex set `U ⊆ ℂ` admits a global primitive on `U`.
-/
theorem convex_differentiableOn_to_isExactOn
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hConv : Convex ℝ U) (hf : DifferentiableOn ℂ f U) :
    IsExactOn f U := by
  obtain ⟨F, hF⟩ := hConv.exists_forall_hasDerivWithinAt hf
  exact ⟨F, fun z hz => (hF z hz).hasDerivAt (hU.mem_nhds hz)⟩

/--
Unfolded primitive witness form of `convex_differentiableOn_to_isExactOn`.
-/
theorem convex_differentiableOn_exists_primitive
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hConv : Convex ℝ U) (hf : DifferentiableOn ℂ f U) :
    ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (f z) z :=
  convex_differentiableOn_to_isExactOn hU hConv hf

/--
Holomorphicity on an open convex set implies zero rectangular holonomy on that set.
-/
theorem convex_differentiableOn_to_zeroRectangularHolonomyOn
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hConv : Convex ℝ U) (hf : DifferentiableOn ℂ f U) :
    ZeroRectangularHolonomyOn f U :=
  primitiveExactOn_to_zeroRectangularHolonomyOn hU
    (convex_differentiableOn_to_isExactOn hU hConv hf)

/--
Holomorphicity on an open convex set gives Mathlib pointwise analyticity at any point of `U`.
-/
theorem convex_differentiableOn_to_analyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hConv : Convex ℝ U) (hz : z ∈ U)
    (hf : DifferentiableOn ℂ f U) :
    AnalyticAt ℂ f z :=
  primitiveExactOn_to_analyticAt hU hz
    (convex_differentiableOn_to_isExactOn hU hConv hf)

/--
Holomorphicity on an open convex set gives the repo Cauchy/Hestenes pointwise analyticity
readback at any point of `U`.
-/
def convex_differentiableOn_to_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hConv : Convex ℝ U) (hz : z ∈ U)
    (hf : DifferentiableOn ℂ f U) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  primitiveExactOn_to_cauchyAnalyticAt hU hz
    (convex_differentiableOn_to_isExactOn hU hConv hf)

/--
Holomorphicity on an open convex set transports to the doubled/clock-axis pointwise
analyticity structure.
-/
def convex_differentiableOn_to_doubled_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hConv : Convex ℝ U) (hz : z ∈ U)
    (hf : DifferentiableOn ℂ f U) :
    CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
      (lifted f) (complexToDoubled z) :=
  primitiveExactOn_to_doubled_cauchyAnalyticAt hU hz
    (convex_differentiableOn_to_isExactOn hU hConv hf)

/-! ## Group B: Star-convex domain primitive exactness (`StarConvex ℝ x₀ U`) -/

/--
A holomorphic function on an open star-convex set `U ⊆ ℂ` admits a global primitive on `U`,
constructed explicitly by radial integration from the star center `x₀`.
-/
theorem starConvex_differentiableOn_to_isExactOn
    {U : Set ℂ} {f : ℂ → ℂ} {x₀ : ℂ}
    (hU : IsOpen U) (hStar : StarConvex ℝ x₀ U) (hf : DifferentiableOn ℂ f U) :
    IsExactOn f U := by
  let F : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..1, (z - x₀) * f (x₀ + (t : ℂ) * (z - x₀))
  refine ⟨F, fun z₀ hz₀ => ?_⟩
  have hseg_sub : segment ℝ x₀ z₀ ⊆ U := hStar.segment_subset hz₀
  have hseg_compact : IsCompact (segment ℝ x₀ z₀) := by
    rw [segment_eq_image' ℝ x₀ z₀]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hseg_compact.exists_thickening_subset_open hU hseg_sub
  let V : Set ℂ := Metric.thickening δ (segment ℝ x₀ z₀)
  have hV_open : IsOpen V := Metric.isOpen_thickening
  have hV_conv : Convex ℝ V := (convex_segment x₀ z₀).thickening δ
  have hz₀V : z₀ ∈ V := Metric.self_subset_thickening hδ_pos _ (right_mem_segment ℝ x₀ z₀)
  have hx₀V : x₀ ∈ V := Metric.self_subset_thickening hδ_pos _ (left_mem_segment ℝ x₀ z₀)
  obtain ⟨G, hG⟩ := convex_differentiableOn_to_isExactOn hV_open hV_conv (hf.mono hδ_sub)
  have hEq : ∀ w ∈ V, F w = G w - G x₀ := by
    intro w hwV
    let γ : ℝ → ℂ := fun t => x₀ + (t : ℂ) * (w - x₀)
    have hγ_mem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, γ t ∈ V := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hmem := hV_conv.add_smul_sub_mem hx₀V hwV ht
      simpa [γ, Complex.real_smul] using hmem
    have hγ_deriv : ∀ t : ℝ, HasDerivAt γ (w - x₀) t := by
      intro t
      have hc : HasDerivAt (fun s : ℂ => x₀ + s * (w - x₀)) (1 * (w - x₀)) (t : ℂ) :=
        ((hasDerivAt_id (t : ℂ)).mul_const (w - x₀)).const_add x₀
      simpa [γ] using hc.comp_ofReal
    have hGγ_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (G ∘ γ) ((w - x₀) * f (γ t)) t := by
      intro t ht
      have hderiv := (hG (γ t) (hγ_mem t ht)).scomp t (hγ_deriv t)
      simpa [smul_eq_mul] using hderiv
    have hcont : ContinuousOn (fun t : ℝ => (w - x₀) * f (γ t)) (Set.Icc (0 : ℝ) 1) := by
      have hfV : ContinuousOn f V := (hf.mono hδ_sub).continuousOn
      have hγ_cont : Continuous γ := by fun_prop
      exact continuousOn_const.mul (hfV.comp hγ_cont.continuousOn (fun t ht =>
        hγ_mem t (by rwa [Set.uIcc_of_le zero_le_one])))
    have hint : IntervalIntegrable (fun t : ℝ => (w - x₀) * f (γ t))
        MeasureTheory.volume 0 1 :=
      hcont.intervalIntegrable_of_Icc zero_le_one
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hGγ_deriv hint
    simpa [F, γ] using hFTC
  exact ((hG z₀ hz₀V).sub_const (G x₀)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hV_open.mem_nhds hz₀V) hEq)

/--
Unfolded primitive witness form of `starConvex_differentiableOn_to_isExactOn`.
-/
theorem starConvex_differentiableOn_exists_primitive
    {U : Set ℂ} {f : ℂ → ℂ} {x₀ : ℂ}
    (hU : IsOpen U) (hStar : StarConvex ℝ x₀ U) (hf : DifferentiableOn ℂ f U) :
    ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (f z) z :=
  starConvex_differentiableOn_to_isExactOn hU hStar hf

/--
Holomorphicity on an open star-convex set implies zero rectangular holonomy on that set.
-/
theorem starConvex_differentiableOn_to_zeroRectangularHolonomyOn
    {U : Set ℂ} {f : ℂ → ℂ} {x₀ : ℂ}
    (hU : IsOpen U) (hStar : StarConvex ℝ x₀ U) (hf : DifferentiableOn ℂ f U) :
    ZeroRectangularHolonomyOn f U :=
  primitiveExactOn_to_zeroRectangularHolonomyOn hU
    (starConvex_differentiableOn_to_isExactOn hU hStar hf)

/--
Holomorphicity on an open star-convex set gives Mathlib pointwise analyticity at any point of `U`.
-/
theorem starConvex_differentiableOn_to_analyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {x₀ z : ℂ}
    (hU : IsOpen U) (hStar : StarConvex ℝ x₀ U) (hz : z ∈ U)
    (hf : DifferentiableOn ℂ f U) :
    AnalyticAt ℂ f z :=
  primitiveExactOn_to_analyticAt hU hz
    (starConvex_differentiableOn_to_isExactOn hU hStar hf)

/--
Holomorphicity on an open star-convex set gives the repo Cauchy/Hestenes pointwise analyticity
readback at any point of `U`.
-/
def starConvex_differentiableOn_to_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {x₀ z : ℂ}
    (hU : IsOpen U) (hStar : StarConvex ℝ x₀ U) (hz : z ∈ U)
    (hf : DifferentiableOn ℂ f U) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  primitiveExactOn_to_cauchyAnalyticAt hU hz
    (starConvex_differentiableOn_to_isExactOn hU hStar hf)

/--
Holomorphicity on an open star-convex set transports to the doubled/clock-axis pointwise
analyticity structure.
-/
def starConvex_differentiableOn_to_doubled_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {x₀ z : ℂ}
    (hU : IsOpen U) (hStar : StarConvex ℝ x₀ U) (hz : z ∈ U)
    (hf : DifferentiableOn ℂ f U) :
    CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
      (lifted f) (complexToDoubled z) :=
  primitiveExactOn_to_doubled_cauchyAnalyticAt hU hz
    (starConvex_differentiableOn_to_isExactOn hU hStar hf)

/--
Slit-plane corollary: a holomorphic function on `Complex.slitPlane` admits a global primitive.
-/
theorem slitPlane_differentiableOn_to_isExactOn
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f slitPlane) :
    IsExactOn f slitPlane :=
  starConvex_differentiableOn_to_isExactOn isOpen_slitPlane starConvex_one_slitPlane hf

/--
Slit-plane corollary: a holomorphic function on `Complex.slitPlane` has zero rectangular holonomy.
-/
theorem slitPlane_differentiableOn_to_zeroRectangularHolonomyOn
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f slitPlane) :
    ZeroRectangularHolonomyOn f slitPlane :=
  starConvex_differentiableOn_to_zeroRectangularHolonomyOn
    isOpen_slitPlane starConvex_one_slitPlane hf

end InfoGeometry.Canonical.PrimitiveExactness
