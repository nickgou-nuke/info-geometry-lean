import InfoGeometry.Spectral.QuantumFluctuations

namespace InfoGeometry.Canonical.QuantumFluctuationsCapstone

open InfoGeometry.Spectral.QuantumFluctuations

theorem capstone_quantum_fluctuations_synthesis (p : ℕ) (m : ℕ) (E T : ℝ)
    (hp : 2 ≤ p) (hm : 1 ≤ m) (hT : Real.exp 1 < T) :
    (primePhaseHarmonic p m 0 = 0) ∧
    (primePhaseHarmonic p m (-E) = - primePhaseHarmonic p m E) ∧
    (0 < selbergVariance T) :=
  grand_quantum_fluctuations_synthesis p m E T hp hm hT

end InfoGeometry.Canonical.QuantumFluctuationsCapstone
