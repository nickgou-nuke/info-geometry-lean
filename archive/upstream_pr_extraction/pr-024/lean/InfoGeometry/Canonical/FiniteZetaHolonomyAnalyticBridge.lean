import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
import InfoGeometry.Canonical.ComplexAnalyticBridge

/-!
# Finite zeta holonomy analytic bridge

This module attaches the existing finite zeta holonomy

`h_p(s) = exp((1 / 2 - s) * log p)`

to Mathlib's native complex analytic surface, then reuses the existing
`ComplexAnalyticBridge` to read it as a Cauchy-analytic map and as a transported
map on the doubled real carrier.

The proof is deliberately local and finite: the only analytic fact used is that
the complex exponential of an affine complex expression is differentiable, hence
analytic by Mathlib's `Differentiable.analyticAt`.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteZetaHolonomyAnalyticBridge

open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
open InfoGeometry.Canonical.ComplexAnalyticBridge
open InfoGeometry.Geometry.BilingualAnalyticity

/--
The finite zeta holonomy at a fixed prime mode is complex analytic.

This is the Mathlib/Weierstrass statement.  It is a direct consequence of
complex differentiability of `s ↦ exp((1 / 2 - s) * log p)`.
-/
theorem zetaHolonomy_analyticAt
    {P : PrimeCutoff} (p : PrimeMode P) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => zetaHolonomy (P := P) z p) s := by
  unfold zetaHolonomy
  have hdiff : Differentiable ℂ
      (fun z : ℂ => Complex.exp (((1 / 2 : ℂ) - z) * Complex.log (p : ℂ))) := by
    fun_prop
  exact hdiff.analyticAt s

/--
The normalized finite prime holonomy is complex analytic.

This is the same finite affine-exponential statement using the real logarithm
normalization already exposed by `PrimeCantorZetaDiracOperator`.
-/
theorem zetaNormalizedPrimeHolonomy_analyticAt
    {P : PrimeCutoff} (p : PrimeMode P) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => zetaNormalizedPrimeHolonomy (P := P) z p) s := by
  unfold zetaNormalizedPrimeHolonomy
  have hdiff : Differentiable ℂ
      (fun z : ℂ =>
        Complex.exp ((((1 / 2 : ℝ) : ℂ) - z) * ((Real.log (p.1 : ℝ) : ℝ) : ℂ))) := by
    fun_prop
  exact hdiff.analyticAt s

/--
The finite zeta holonomy satisfies the repository's Cauchy-analytic socket.

This is only the honest one-way bridge: native Mathlib `AnalyticAt` implies the
repo's derivative-plus-phase-linearity formulation.
-/
def zetaHolonomy_cauchyAnalyticAt
    {P : PrimeCutoff} (p : PrimeMode P) (s : ℂ) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure
      (fun z : ℂ => zetaHolonomy (P := P) z p) s :=
  analyticAtToCauchyAnalyticAt (zetaHolonomy_analyticAt p s)

/--
The normalized finite prime holonomy satisfies the repository's Cauchy-analytic
socket by the same one-way bridge.
-/
def zetaNormalizedPrimeHolonomy_cauchyAnalyticAt
    {P : PrimeCutoff} (p : PrimeMode P) (s : ℂ) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure
      (fun z : ℂ => zetaNormalizedPrimeHolonomy (P := P) z p) s :=
  analyticAtToCauchyAnalyticAt (zetaNormalizedPrimeHolonomy_analyticAt p s)

/--
Transport the finite zeta holonomy to the doubled real carrier with the canonical
clock-axis phase structure.
-/
def zetaHolonomy_lifted_doubled_cauchyAnalyticAt
    {P : PrimeCutoff} (p : PrimeMode P) (s : ℂ) :
    CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
      (lifted (fun z : ℂ => zetaHolonomy (P := P) z p)) (complexToDoubled s) :=
  analyticAt_liftedToDoubled_cauchyAnalyticAt (zetaHolonomy_analyticAt p s)

/--
Transport the normalized finite prime holonomy to the doubled real carrier with
the canonical clock-axis phase structure.
-/
def zetaNormalizedPrimeHolonomy_lifted_doubled_cauchyAnalyticAt
    {P : PrimeCutoff} (p : PrimeMode P) (s : ℂ) :
    CauchyAnalyticAt doubledPhaseStructure doubledPhaseStructure
      (lifted (fun z : ℂ => zetaNormalizedPrimeHolonomy (P := P) z p))
      (complexToDoubled s) :=
  analyticAt_liftedToDoubled_cauchyAnalyticAt
    (zetaNormalizedPrimeHolonomy_analyticAt p s)

end InfoGeometry.Canonical.FiniteZetaHolonomyAnalyticBridge

