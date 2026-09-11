import InfoGeometry.Spectral.QuantumFluctuations
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.QuantumFluctuationsCapstone

open InfoGeometry.Spectral.QuantumFluctuations

theorem capstone_quantum_fluctuations_synthesis (p : ℕ) (m : ℕ) (E T : ℝ)
    (hp : 2 ≤ p) (hm : 1 ≤ m) (hT : Real.exp 1 < T) :
    (primePhaseHarmonic p m 0 = 0) ∧
    (primePhaseHarmonic p m (-E) = - primePhaseHarmonic p m E) ∧
    (0 < selbergVariance T) := by
  exact ⟨prime_phase_harmonic_at_zero p m,
    prime_phase_harmonic_odd p m E,
    selberg_variance_pos T hT⟩

end InfoGeometry.Canonical.QuantumFluctuationsCapstone
