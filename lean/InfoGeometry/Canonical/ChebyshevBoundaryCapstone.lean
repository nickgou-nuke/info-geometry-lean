import InfoGeometry.Spectral.ChebyshevBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ChebyshevBoundaryCapstone

open InfoGeometry.Spectral.ChebyshevBoundary

theorem capstone_chebyshev_boundary_synthesis (x γ : ℝ) (hx : 0 < x) :
    (Complex.normSq (criticalZero γ) = 1 / 4 + γ ^ 2) ∧
    (criticalZero γ ≠ 0) ∧
    (Complex.exp (criticalZero γ * ((Real.log x : ℝ) : ℂ)) =
     ((Real.sqrt x : ℝ) : ℂ) * Complex.exp (Complex.I * ((γ * Real.log x : ℝ) : ℂ))) :=
  grand_chebyshev_boundary_synthesis x γ hx

end InfoGeometry.Canonical.ChebyshevBoundaryCapstone

