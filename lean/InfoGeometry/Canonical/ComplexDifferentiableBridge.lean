import InfoGeometry.Canonical.ComplexAnalyticBridge

/-!
# Complex differentiability bridge

This module records the safest one-way bridge from neighborhood complex
Fréchet differentiability to the repository's Cauchy/Hestenes analyticity
interfaces.

No converse is asserted here.  In particular, this file does not claim that a
real phase-linear derivative by itself reconstructs Mathlib power-series
analyticity.

#### BUCKET 1: CLOSED FINITE THEOREMS
`eventually_differentiableAt_to_analyticAt` is a direct re-export of Mathlib's
local complex differentiability characterization of `AnalyticAt`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`eventually_differentiableAt_to_cauchyAnalyticAt` and
`eventually_differentiableAt_to_doubled_cauchyAnalyticAt` depend only on the
explicit neighborhood differentiability premise
`∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x`.

#### BUCKET 3: OPEN CLOSURE DEBT
None.  The converse direction from repo phase-linearity to Mathlib
power-series analyticity is intentionally not claimed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ComplexDifferentiableBridge

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.ComplexAnalyticBridge
open scoped _root_.Topology

/--
Neighborhood complex differentiability implies Mathlib `AnalyticAt`.

This is Mathlib's local differentiability characterization of complex
analyticity, re-exported under the bridge namespace.
-/
theorem eventually_differentiableAt_to_analyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (h_diff : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x) :
    AnalyticAt ℂ f z :=
  eventuallyDifferentiableAtToAnalyticAt h_diff

/--
Neighborhood complex differentiability implies the repo pointwise
`CauchyAnalyticAt` structure on the native complex phase structure.
-/
def eventually_differentiableAt_to_cauchyAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (h_diff : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure f z :=
  analyticAtToCauchyAnalyticAt
    (eventually_differentiableAt_to_analyticAt h_diff)

/--
Neighborhood complex differentiability implies repo `CauchyAnalyticAt` after
transport to the real doubled carrier.

The derivative is transported through the continuous real-linear equivalence
`complexDoubledCLE`, and phase-linearity is exactly clock-axis compatibility.
-/
def eventually_differentiableAt_to_doubled_cauchyAnalyticAt
    {f : ℂ → ℂ} {z : ℂ}
    (h_diff : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x) :
    CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
      (lifted f) (complexToDoubled z) :=
  analyticAt_liftedToDoubled_cauchyAnalyticAt
    (eventually_differentiableAt_to_analyticAt h_diff)

end InfoGeometry.Canonical.ComplexDifferentiableBridge
