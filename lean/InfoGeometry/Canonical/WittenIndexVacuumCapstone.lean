import InfoGeometry.Quantum.WittenIndexVacuum
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.WittenIndexVacuumCapstone

open InfoGeometry.Quantum.WittenIndexVacuum

/-- Canonical finite vacuum packet: excited levels cancel, the thermal index is
    constant, the unique vacuum index is one, and conjugate prime phases cancel. -/
theorem capstone_witten_index_vacuum_synthesis
    (E β γ p : ℝ) :
    (excitedLevelWittenContribution E β = 0) ∧
    (HasDerivAt (wittenIndexThermal 1 0) 0 β) ∧
    (wittenIndex 1 0 = 1) ∧
    ((Complex.exp (Complex.I * (γ * Real.log p : ℂ))) *
     (Complex.exp (-Complex.I * (γ * Real.log p : ℂ))) = 1) := by
  exact ⟨excited_level_witten_cancels E β,
    hasDerivAt_witten_index_zero 1 0 β,
    witten_index_unique_vacuum,
    susy_prime_phase_cancellation γ p⟩

end InfoGeometry.Canonical.WittenIndexVacuumCapstone
