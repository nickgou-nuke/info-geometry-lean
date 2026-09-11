import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
/-!
# Applications of Euler Sums and Series Involving the Zeta Functions
Formalizes the series representations from the 2023 Symmetry paper
"Applications of Euler Sums and Series Involving the Zeta Functions" by Choi and Sofo.
It includes definitions of the Mathieu series and its relation to the Riemann Zeta function,
as well as the logarithmic representation of Wallis's infinite product for π.
-/
noncomputable section
namespace InfoGeometry.Analysis.EulerZetaSeries
open Real
/-- The formal Dirichlet-series expression used by this interface.  No
    convergence or identification with `riemannZeta` is asserted here. -/
def formalRiemannZetaSeries (s : ℝ) : ℝ :=
  ∑' (n : ℕ), if n = 0 then 0 else 1 / (n : ℝ)^s
/-- The Mathieu Series defined for τ > 0 (Eq 94). -/
def mathieu_series (τ : ℝ) : ℝ :=
  ∑' (ξ : ℕ), if ξ = 0 then 0 else (2 * (ξ : ℝ)) / (((ξ : ℝ)^2 + τ^2)^2)
/-- 
Proposition: The Mathieu series admits an expansion in terms of the Riemann Zeta function
for |τ| < 1 (Eq 98 in the paper).
-/
def mathieu_zeta_expansion_prop (τ : ℝ) : Prop :=
  (|τ| < 1) → mathieu_series τ = 2 * ∑' (n : ℕ), if n = 0 then 0 else
    (-1)^(n - 1) * (n : ℝ) * (formalRiemannZetaSeries (2 * n + 1)) *
      τ^(2 * (n - 1))
/-- 
Wallis's infinite product formula evaluates to π / 2.
Taking the logarithm yields an expansion in terms of Zeta functions (Eq 89).
-/
def wallis_log_zeta_expansion_prop : Prop :=
  Real.log (Real.pi / 2) = ∑' (τ : ℕ), if τ = 0 then 0 else
    (formalRiemannZetaSeries (2 * τ)) / ((τ : ℝ) * 2^(2 * τ))
end InfoGeometry.Analysis.EulerZetaSeries
