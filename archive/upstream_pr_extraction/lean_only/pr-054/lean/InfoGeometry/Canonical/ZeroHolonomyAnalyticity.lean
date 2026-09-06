import Mathlib.Analysis.Complex.HasPrimitives
import InfoGeometry.Canonical.ComplexAnalyticBridge

/-!
# Zero-holonomy analyticity

This file gives the theorem-safe part of the gauge-theoretic reading of
Morera's theorem.

Mathlib's `Complex.IsConservativeOn` is not an arbitrary-path Wilson-loop API;
it is a rectangle/wedge-integral API.  We therefore formalize the exact bridge:
zero rectangular holonomy is equivalent to Mathlib's conservative/Morera
condition.  Arbitrary Berry phases or path-ordered Wilson loops require extra
structure and are intentionally not postulated here.

#### BUCKET 1: CLOSED FINITE THEOREMS
Zero rectangular holonomy is proved equivalent to Mathlib's
`Complex.IsConservativeOn`, and complex-linear infinitesimal generators are
proved to commute with the canonical complex phase axis.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`zeroRectangularHolonomyOn_to_analyticAt` and
`zeroRectangularHolonomyOn_to_cauchyAnalyticAt` depend only on explicit
openness, membership, zero-rectangular-holonomy, and continuity hypotheses.

#### BUCKET 3: OPEN CLOSURE DEBT
No arbitrary Wilson-loop, Berry-phase, curvature-flatness, or global gauge
connection theorem is claimed.  Those require additional formal structures not
provided by Mathlib's `Complex.IsConservativeOn`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZeroHolonomyAnalyticity

open Complex
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.ComplexAnalyticBridge
open scoped Topology

/--
The rectangle holonomy/readout of a complex field around the boundary of the
axis-aligned rectangle with opposite corners `z` and `w`.

Mathlib packages this contour as two opposite `wedgeIntegral`s.  Vanishing of
this quantity is exactly the conservative/Morera condition used in
`Complex.IsConservativeOn`.
-/
def rectangularWilsonLoop (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  wedgeIntegral z w f + wedgeIntegral w z f

/-- Zero rectangular holonomy on a domain. -/
def ZeroRectangularHolonomyOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ z w, Rectangle z w ⊆ U → rectangularWilsonLoop f z w = 0

/-- Mathlib conservativity/Morera implies zero rectangular holonomy. -/
theorem zeroRectangularHolonomyOn_of_isConservativeOn
    {f : ℂ → ℂ} {U : Set ℂ}
    (hf : IsConservativeOn f U) :
    ZeroRectangularHolonomyOn f U := by
  intro z w hrect
  unfold rectangularWilsonLoop
  rw [hf z w hrect, neg_add_cancel]

/-- Zero rectangular holonomy implies Mathlib conservativity/Morera. -/
theorem isConservativeOn_of_zeroRectangularHolonomyOn
    {f : ℂ → ℂ} {U : Set ℂ}
    (hf : ZeroRectangularHolonomyOn f U) :
    IsConservativeOn f U := by
  intro z w hrect
  exact add_eq_zero_iff_eq_neg.mp (hf z w hrect)

/-- The exact theorem-safe equivalence: Morera conservativity is zero rectangle holonomy. -/
theorem isConservativeOn_iff_zeroRectangularHolonomyOn
    {f : ℂ → ℂ} {U : Set ℂ} :
    IsConservativeOn f U ↔ ZeroRectangularHolonomyOn f U :=
  ⟨zeroRectangularHolonomyOn_of_isConservativeOn,
    isConservativeOn_of_zeroRectangularHolonomyOn⟩

/--
Zero rectangular holonomy plus continuity on an open set gives Mathlib
`AnalyticAt`, via Morera's theorem as formalized in mathlib.
-/
theorem zeroRectangularHolonomyOn_to_analyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (hZero : ZeroRectangularHolonomyOn f U)
    (hCont : ContinuousOn f U) :
    AnalyticAt ℂ f z :=
  moreraOnOpenToAnalyticAt hU hz
    (isConservativeOn_of_zeroRectangularHolonomyOn hZero) hCont

/--
Zero rectangular holonomy plus continuity on an open set lands in the repo
Cauchy/Hestenes pointwise analyticity structure.
-/
def zeroRectangularHolonomyOn_to_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (hZero : ZeroRectangularHolonomyOn f U)
    (hCont : ContinuousOn f U) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  analyticAtToCauchyAnalyticAt
    (zeroRectangularHolonomyOn_to_analyticAt hU hz hZero hCont)

/-! ## Primitive/exactness route -/

/--
Primitive exactness (`f` has a local primitive on `U`) implies complex
differentiability on the open set.
-/
theorem differentiableOn_of_isExactOn
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hExact : IsExactOn f U) :
    DifferentiableOn ℂ f U :=
  hExact.differentiableOn hU

/--
Primitive exactness on an open set implies Mathlib `AnalyticAt` at each point
of that set.
-/
theorem isExactOn_to_analyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : IsExactOn f U) :
    AnalyticAt ℂ f z :=
  (differentiableOn_of_isExactOn hU hExact).analyticAt (hU.mem_nhds hz)

/--
Primitive exactness on an open set lands in the repo Cauchy/Hestenes pointwise
analyticity structure.
-/
def isExactOn_to_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : IsExactOn f U) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  analyticAtToCauchyAnalyticAt (isExactOn_to_analyticAt hU hz hExact)

/-- Primitive exactness implies Mathlib conservativity on the same open set. -/
theorem isConservativeOn_of_isExactOn
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hExact : IsExactOn f U) :
    IsConservativeOn f U :=
  (differentiableOn_of_isExactOn hU hExact).isConservativeOn

/-- Primitive exactness implies zero rectangular holonomy. -/
theorem zeroRectangularHolonomyOn_of_isExactOn
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hExact : IsExactOn f U) :
    ZeroRectangularHolonomyOn f U :=
  zeroRectangularHolonomyOn_of_isConservativeOn
    (isConservativeOn_of_isExactOn hU hExact)

/--
Primitive exactness is a sufficient zero-holonomy analyticity property.
-/
def primitiveExactness_to_zeroHolonomy_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : IsExactOn f U) :
    ZeroRectangularHolonomyOn f U ∧
      Nonempty (CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z) :=
  ⟨zeroRectangularHolonomyOn_of_isExactOn hU hExact,
    ⟨isExactOn_to_cauchyAnalyticAt hU hz hExact⟩⟩

/--
Primitive exactness on an open set also transports to the doubled/clock-axis
pointwise analyticity structure.
-/
def isExactOn_to_doubled_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : IsExactOn f U) :
    CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
      (lifted f) (complexToDoubled z) :=
  analyticAt_liftedToDoubled_cauchyAnalyticAt
    (isExactOn_to_analyticAt hU hz hExact)

/--
Primitive exactness is also a sufficient doubled-space zero-holonomy
analyticity property.
-/
def primitiveExactness_to_zeroHolonomy_doubled_cauchyAnalyticAt
    {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hExact : IsExactOn f U) :
    ZeroRectangularHolonomyOn f U ∧
      Nonempty
        (CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
          (lifted f) (complexToDoubled z)) :=
  ⟨zeroRectangularHolonomyOn_of_isExactOn hU hExact,
    ⟨isExactOn_to_doubled_cauchyAnalyticAt hU hz hExact⟩⟩

/--
Linear infinitesimal holomorphic generators commute with the complex phase axis.

This is the rigorous algebraic version of `[X, K] = 0`: if the infinitesimal
generator is genuinely complex-linear, then its real restriction is phase-linear
for the canonical complex phase structure.
-/
theorem complexLinearGenerator_commutes_phaseAxis
    (X : ℂ →L[ℂ] ℂ) :
    complexPhaseStructure.IsPhaseLinearMap
      (X.restrictScalars ℝ) complexPhaseStructure :=
  complexLinearMap_phaseLinear X

/-- Pointwise version of commutation with the complex phase axis. -/
theorem complexLinearGenerator_commutes_complexIMap
    (X : ℂ →L[ℂ] ℂ) (z : ℂ) :
    (X.restrictScalars ℝ) (complexIMap z) =
      complexIMap ((X.restrictScalars ℝ) z) := by
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L z)
    (complexLinearGenerator_commutes_phaseAxis X)

/--
For a repo `CauchyAnalyticAt` property, the stored derivative commutes with the
phase axis.  This is the derivative-level Cauchy-Riemann/clock-axis law.
-/
theorem cauchyAnalyticAt_derivative_commutes_phaseAxis
    {F : ℂ → ℂ} {z : ℂ}
    (hF : CauchyAnalyticAt complexPhaseStructure complexPhaseStructure F z)
    (v : ℂ) :
    hF.deriv (complexPhaseStructure.K v) =
      complexPhaseStructure.K (hF.deriv v) := by
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hF.phase_linear_deriv

end InfoGeometry.Canonical.ZeroHolonomyAnalyticity
