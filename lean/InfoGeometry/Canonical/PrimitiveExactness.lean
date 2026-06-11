import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import InfoGeometry.Canonical.ZeroHolonomyAnalyticity

/-!
# Primitive exactness

This file records the theorem-safe primitive/exactness formulation of complex
analyticity.

We deliberately do **not** introduce an axiomatic global partition function or a
blanket global primitive theorem.  The formal owner is Mathlib's
`Complex.IsExactOn`: a field is primitive-exact on `U` when it has a primitive
on `U`.  Mathlib then supplies the safe routes:

* differentiability on a ball gives primitive exactness on that ball;
* primitive exactness on an open set gives differentiability and analyticity;
* primitive exactness implies Morera conservativity and zero rectangular
  holonomy through `ZeroHolonomyAnalyticity`.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimitiveExactness

open Complex
open Metric
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.ComplexAnalyticBridge
open InfoGeometry.Canonical.ZeroHolonomyAnalyticity
open scoped Topology

/-- Repository-facing name for Mathlib's primitive/exactness predicate. -/
abbrev PrimitiveExactOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  IsExactOn f U

/-- A proof-carrying primitive potential on a domain. -/
structure PrimitivePotentialOn (f : ℂ → ℂ) (U : Set ℂ) where
  potential : ℂ → ℂ
  hasDerivAt_potential : ∀ z ∈ U, HasDerivAt potential (f z) z

/-- Convert the explicit primitive-potential structure to Mathlib `IsExactOn`. -/
theorem PrimitivePotentialOn.to_isExactOn
    {f : ℂ → ℂ} {U : Set ℂ}
    (P : PrimitivePotentialOn f U) :
    PrimitiveExactOn f U :=
  ⟨P.potential, P.hasDerivAt_potential⟩

/-- Convert Mathlib `IsExactOn` to an explicit primitive-potential package. -/
theorem primitivePotentialOn_of_isExactOn
    {f : ℂ → ℂ} {U : Set ℂ}
    (hExact : PrimitiveExactOn f U) :
    Nonempty (PrimitivePotentialOn f U) := by
  rcases hExact with ⟨F, hF⟩
  exact ⟨{ potential := F, hasDerivAt_potential := hF }⟩

/-- A complex differentiable field on a ball has a primitive on that ball. -/
theorem differentiableOn_ball_to_primitiveExactOn
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) :
    PrimitiveExactOn f (ball c r) :=
  hf.isExactOn_ball

/-- A globally complex differentiable field has a primitive on every ball. -/
theorem differentiable_to_primitiveExactOn_ball
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) (r : ℝ) :
    PrimitiveExactOn f (ball c r) :=
  differentiableOn_ball_to_primitiveExactOn (hf.differentiableOn.mono subset_univ)

/-- Primitive exactness on an open set gives complex differentiability there. -/
theorem primitiveExactOn_to_differentiableOn
    {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hExact : PrimitiveExactOn f U) :
    DifferentiableOn ℂ f U :=
  hExact.differentiableOn hU

/-- Primitive exactness on an open set gives Mathlib pointwise analyticity. -/
theorem primitiveExactOn_to_analyticAt
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : PrimitiveExactOn f U) :
    AnalyticAt ℂ f z :=
  isExactOn_to_analyticAt hU hz hExact

/-- Primitive exactness on an open set lands in the repo Cauchy-analytic structure. -/
def primitiveExactOn_to_cauchyAnalyticAt
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : PrimitiveExactOn f U) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  isExactOn_to_cauchyAnalyticAt hU hz hExact

/-- Primitive exactness implies Mathlib Morera conservativity on an open set. -/
theorem primitiveExactOn_to_isConservativeOn
    {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hExact : PrimitiveExactOn f U) :
    IsConservativeOn f U :=
  isConservativeOn_of_isExactOn hU hExact

/-- Primitive exactness implies zero rectangular holonomy. -/
theorem primitiveExactOn_to_zeroRectangularHolonomyOn
    {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hExact : PrimitiveExactOn f U) :
    ZeroRectangularHolonomyOn f U :=
  zeroRectangularHolonomyOn_of_isExactOn hU hExact

/--
A primitive potential is analytic at every point of an open exactness domain.
-/
theorem PrimitivePotentialOn.analyticAt_potential
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (P : PrimitivePotentialOn f U) (hU : IsOpen U) (hz : z ∈ U) :
    AnalyticAt ℂ P.potential z := by
  have hdiff : DifferentiableOn ℂ P.potential U :=
    fun w hw => (P.hasDerivAt_potential w hw).differentiableAt.differentiableWithinAt
  exact hdiff.analyticAt (hU.mem_nhds hz)

/--
Primitive exactness supplies a locally analytic primitive potential.
-/
theorem primitiveExactOn_exists_analyticAt_potential
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : PrimitiveExactOn f U) :
    ∃ F : ℂ → ℂ,
      (∀ w ∈ U, HasDerivAt F (f w) w) ∧ AnalyticAt ℂ F z := by
  rcases hExact with ⟨F, hF⟩
  refine ⟨F, hF, ?_⟩
  exact (PrimitivePotentialOn.analyticAt_potential
    ({ potential := F, hasDerivAt_potential := hF } : PrimitivePotentialOn f U) hU hz)

/--
Compact certificate: on an open set, primitive exactness yields zero rectangular
holonomy and repo Cauchy analyticity at every chosen point.
-/
def primitiveExactnessCertificate
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : PrimitiveExactOn f U) :
    ZeroRectangularHolonomyOn f U ∧
      Nonempty (CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z) :=
  primitiveExactness_to_zeroHolonomy_cauchyAnalyticAt hU hz hExact

end InfoGeometry.Canonical.PrimitiveExactness
