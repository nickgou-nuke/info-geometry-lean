import InfoGeometry.Quantum.BosonFockReciprocity

namespace InfoGeometry.Canonical.BosonFockReciprocityCapstone

open InfoGeometry.Quantum.BosonFockReciprocity

theorem capstone_susy_reciprocity_synthesis (p : ℕ) (hp : Nat.Prime p) (s : ℂ)
    (hs : primeFermionicFactor p s ≠ 0) :
    (primeFermionicFactor p s ≠ 0) ∧
    (primeSusyPartitionFunction p s = 1) ∧
    (primeFermionicFactor p s = (primeBosonicFactor p s)⁻¹) :=
  grand_susy_reciprocity_synthesis p hp s hs

end InfoGeometry.Canonical.BosonFockReciprocityCapstone
