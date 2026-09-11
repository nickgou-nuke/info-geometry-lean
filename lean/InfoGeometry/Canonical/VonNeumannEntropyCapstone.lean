import InfoGeometry.Thermal.VonNeumannEntropy
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.VonNeumannEntropyCapstone

open InfoGeometry.Thermal.VonNeumannEntropy

theorem capstone_von_neumann_entropy_synthesis (p : ℕ) (β : ℝ)
    (hp : 2 ≤ p) (hβ : 0 < β) :
    probVacuum p β + probOccupied p β = 1 := by
  exact prob_sum_eq_one p β hp

end InfoGeometry.Canonical.VonNeumannEntropyCapstone
