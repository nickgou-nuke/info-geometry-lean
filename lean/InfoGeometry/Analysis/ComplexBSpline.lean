import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.IndividuatedBoundedTransform
/-!
# Complex B-splines and Hurwitz Zeta Functions
Formalizes the fundamental structural definitions and representations for cardinal
B-splines of complex order, as derived by Forster, Garunkstis, Massopust, and Steuding (2013).
-/
noncomputable section
namespace InfoGeometry.Analysis.ComplexBSpline
open Complex
/-- The formal Dirichlet-series expression used by this finite interface.  No
    convergence or analytic-continuation theorem is asserted here. -/
def formalHurwitzZetaSeries (s : ℂ) (a : ℝ) : ℂ :=
  ∑' (n : ℕ), 1 / ((n : ℂ) + a) ^ s
/--
The interpolation sum denominator built from the formal Dirichlet-series
expressions above.
-/
def f_plus (s : ℂ) (α : ℝ) : ℂ :=
  formalHurwitzZetaSeries s α +
    Complex.exp (-I * Real.pi * s) * formalHurwitzZetaSeries s (1 - α)
/-- A proposition-shaped obligation for the analytic interpolation identity.
    It is intentionally left as data rather than asserted as a theorem until
    convergence and continuation hypotheses are supplied. -/
def spline_interpolation_denominator_prop (s : ℂ) (α : ℝ) : Prop :=
  (0 < α ∧ α < 1 ∧ 1 < s.re) →
  (∑' (k : ℤ), 1 / ((k : ℂ) + α) ^ s) = f_plus s α
end InfoGeometry.Analysis.ComplexBSpline
