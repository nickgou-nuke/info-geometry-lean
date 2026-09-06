import InfoGeometry.Arithmetic.ActualRiemannXiRegularityBridge
import InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
import Mathlib.Analysis.Calculus.Deriv.Star
import InfoGeometry.Topology.ZetaLogDerivativeDeRhamPeriodBridge

/-!
# Actual `riemannXi` logarithmic-derivative coefficient

This owner connects Mathlib's concrete `riemannXi` and its proved reflection
law to the algebraic coefficient `omegaForm`.  It does not construct a
differential form, a contour integral, a de Rham cohomology class, or an
analytic period theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.ActualRiemannXiLogDerivative

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiRegularityBridge
open InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
open InfoGeometry.Topology.ZetaLogDerivativeDeRhamPeriod

/-- The actual coefficient `-ξ'(s) / ξ(s)`, with Lean's totalized division. -/
def actualXiOmegaForm (s : ℂ) : ℂ :=
  omegaForm (riemannXi s) (deriv riemannXi s)

@[simp] theorem actualXiOmegaForm_apply (s : ℂ) :
    actualXiOmegaForm s = -(deriv riemannXi s / riemannXi s) := rfl

/-!
The reflection statement is an equality of actual logarithmic-derivative
coefficients.  The hypotheses exclude the two exceptional points of the
regularity owner; no zero-divisor or contour claim is made here.
-/
theorem actualXiOmegaForm_one_sub
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    actualXiOmegaForm (1 - s) = -actualXiOmegaForm s := by
  unfold actualXiOmegaForm omegaForm
  rw [riemannXi_logDerivative_one_sub hs0 hs1]

/-!
The next two statements use the concrete Schwarz law together with the
regularity owner.  They remain pointwise coefficient identities on the
regular locus; no differential-form or contour structure is introduced.
-/

theorem actualRiemannXi_deriv_conj_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    deriv riemannXi (star s) = star (deriv riemannXi s) := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hderiv : HasDerivAt riemannXi (deriv riemannXi s) s :=
    hasDerivAt_riemannXi_of_one_lt_re hs
  have hstar := HasDerivAt.star_conj hderiv
  have hcongr :
      HasDerivAt riemannXi (star (deriv riemannXi s)) (star s) := by
    apply hstar.congr_of_eventuallyEq
    filter_upwards [] with z
    change riemannXi z = star (riemannXi (star z))
    rw [actualRiemannXi_conj]
    simp
  exact hcongr.deriv

theorem actualXiOmegaForm_conj_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    actualXiOmegaForm (star s) = star (actualXiOmegaForm s) := by
  unfold actualXiOmegaForm omegaForm
  rw [actualRiemannXi_deriv_conj_of_one_lt_re hs,
    actualRiemannXi_conj]
  simp

end InfoGeometry.Topology.ActualRiemannXiLogDerivative
