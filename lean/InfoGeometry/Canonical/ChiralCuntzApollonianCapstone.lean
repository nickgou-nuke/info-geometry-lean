import InfoGeometry.Quantum.ChiralCuntzApollonian
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ChiralCuntzApollonianCapstone

open InfoGeometry.Quantum.ChiralCuntzApollonian

theorem capstone_chiral_cuntz_apollonian_synthesis (γ ξ θ p : ℝ) :
    (tiltCoordinateGenerator ξ θ = ξ) ∧
    (shiftCoordinateGenerator ξ θ = θ) ∧
    (chiralPrimeOperator γ ξ θ = Complex.exp (Complex.I * ((γ * θ : ℝ) : ℂ))) ∧
    (‖chiralPrimeOperator γ ξ θ‖ = 1) ∧
    (chiralPrimeOperator γ ξ (Real.log p) =
      Complex.exp (Complex.I * ((γ * Real.log p : ℝ) : ℂ))) := by
  exact ⟨tilt_generator_eq_rapidity ξ θ,
    shift_generator_eq_angle ξ θ,
    chiral_prime_operator_eq_angular_phase γ ξ θ,
    chiral_prime_operator_unitary γ ξ θ,
    chiral_prime_geodesic_phase γ ξ p⟩

end InfoGeometry.Canonical.ChiralCuntzApollonianCapstone
