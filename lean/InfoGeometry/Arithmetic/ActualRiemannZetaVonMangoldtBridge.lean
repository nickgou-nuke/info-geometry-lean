import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Actual von Mangoldt logarithmic derivative of `riemannZeta`

This owner exposes Mathlib's convergent-half-plane theorem at the repository
boundary.  It does not assert analytic continuation, an explicit formula, or
any zero-counting statement.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge

open scoped LSeries.notation
open ArithmeticFunction

def actualRiemannZetaLogDerivative (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

theorem vonMangoldt_LSeries_eq_actualRiemannZetaLogDerivative
    {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s = actualRiemannZetaLogDerivative s := by
  simpa [actualRiemannZetaLogDerivative] using
    (LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)

theorem actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    actualRiemannZetaLogDerivative s = L ↗Λ s := by
  exact (vonMangoldt_LSeries_eq_actualRiemannZetaLogDerivative hs).symm

end InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
