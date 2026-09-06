import InfoGeometry.Thermal.VonNeumannEntropy

namespace InfoGeometry.Canonical.VonNeumannEntropyCapstone

open InfoGeometry.Thermal.VonNeumannEntropy

theorem capstone_von_neumann_entropy_synthesis (p : ℕ) (β : ℝ) (hp : 2 ≤ p) (hβ : 0 < β) :
    probVacuum p β + probOccupied p β = 1 :=
  grand_von_neumann_entropy_synthesis p β hp hβ

end InfoGeometry.Canonical.VonNeumannEntropyCapstone
