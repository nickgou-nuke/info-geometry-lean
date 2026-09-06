import InfoGeometry.Quantum.ChiralCantorRandomWalk

namespace InfoGeometry.Canonical.ChiralCantorRandomWalkCapstone

open InfoGeometry.Quantum.ChiralCantorRandomWalk

theorem capstone_chiral_cantor_random_walk_synthesis {n : ℕ} (state : BiCantorState n)
    (w : ChiralBitWord n n)
    (h_symm : state.left = state.right)
    (h_balanced : wordDisplacement w.1 = wordDisplacement w.2)
    (σ : ℝ) (h_balance : σ - 1 / 2 = 0) :
    (paritySwap (paritySwap state) = state) ∧
    (chiralCharge (paritySwap state) = -chiralCharge state) ∧
    (chiralCharge state = 0) ∧
    (numberL state = numberR state) ∧
    (lightConeU w * lightConeV w = (chiralScale n n) ^ 2 - (chiralRapidity w) ^ 2) ∧
    (chiralCylinderWeight n n = (1 / 2 : ℝ) ^ (n + n)) ∧
    (chiralRapidity w = 0) ∧
    (σ = 1 / 2) :=
  grand_chiral_cantor_random_walk_synthesis state w h_symm h_balanced σ h_balance

end InfoGeometry.Canonical.ChiralCantorRandomWalkCapstone
