import InfoGeometry.Quantum.PoincareBlochEquator
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.PoincareBlochEquatorCapstone

open InfoGeometry.Quantum.PoincareBlochEquator

/-- The equatorial Bloch condition is exactly the critical affine coordinate,
    together with the repository's fixed vacuum zero-point value. -/
theorem capstone_poincare_bloch_synthesis (σ : ℝ)
    (h_equator : isEquatorialBlochState (σ - 1 / 2)) :
    (stokesCircularAsymmetry (σ - 1 / 2) = 0 ↔ σ - 1 / 2 = 0) ∧
    (σ = 1 / 2) ∧
    (vacuumZeroPointEnergy = 1 / 2) := by
  refine ⟨stokes_asymmetry_zero_iff (σ - 1 / 2), ?_, vacuum_energy_equals_critical_pole⟩
  exact poincare_equator_critical_line σ h_equator

end InfoGeometry.Canonical.PoincareBlochEquatorCapstone
