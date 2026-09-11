import Mathlib.Analysis.Complex.HasPrimitives
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

end InfoGeometry.Canonical.PrimitiveExactness
