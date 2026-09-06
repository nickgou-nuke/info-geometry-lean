import InfoGeometry.Quantum.ChiralCuntzApollonian

namespace InfoGeometry.Canonical.ChiralCuntzApollonianCapstone

open InfoGeometry.Quantum.ChiralCuntzApollonian

theorem capstone_chiral_cuntz_apollonian_synthesis (γ ξ θ p : ℝ) :
    (tiltCoordinateGenerator ξ θ = ξ) ∧
    (shiftCoordinateGenerator ξ θ = θ) ∧
    (chiralPrimeOperator γ ξ θ = Complex.exp (Complex.I * ((γ * θ : ℝ) : ℂ))) ∧
    (‖chiralPrimeOperator γ ξ θ‖ = 1) ∧
    (chiralPrimeOperator γ ξ (Real.log p) =
     Complex.exp (Complex.I * ((γ * Real.log p : ℝ) : ℂ))) :=
  grand_chiral_cuntz_apollonian_synthesis γ ξ θ p

end InfoGeometry.Canonical.ChiralCuntzApollonianCapstone
