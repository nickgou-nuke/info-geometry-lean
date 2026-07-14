import Mathlib
import InfoGeometry.OperatorAlgebra.IndividuatedBoundedTransform

/-!
# Complex B-splines and Hurwitz Zeta Functions

Formalizes the fundamental structural definitions and representations for cardinal
B-splines of complex order, as derived by Forster, Garunkstis, Massopust, and Steuding (2013).
-/

noncomputable section

namespace ComplexBSpline

open Complex

/--
A dummy placeholder for the Hurwitz Zeta function since it may not be in Mathlib.
-/
def hurwitz_zeta (s : ℂ) (a : ℝ) : ℂ := ∑' (n : ℕ), 1 / ((n : ℂ) + a) ^ s

/--
The interpolation sum denominator defined by the Hurwitz zeta functions (Eq 7).
f_+(s, alpha) = zeta(s, alpha) + e^{-i pi s} zeta(s, 1 - alpha)
-/
def f_plus (s : ℂ) (α : ℝ) : ℂ :=
  hurwitz_zeta s α + Complex.exp (-I * Real.pi * s) * hurwitz_zeta s (1 - α)

/--
Proposition: The Fourier representation of the cardinal complex B-spline interpolation
denominator coincides with the sum of two Hurwitz zeta functions in f_plus.
sum_{k in Z} 1/(k + alpha)^s = f_plus(s, alpha)
-/
def spline_interpolation_denominator_prop (s : ℂ) (α : ℝ) : Prop :=
  (0 < α ∧ α < 1 ∧ 1 < s.re) →
  (∑' (k : ℤ), 1 / ((k : ℂ) + α) ^ s) = f_plus s α

end ComplexBSpline
