/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Cantor.BidirectionalChiralRandomWalk

namespace InfoGeometry.Canonical

open InfoGeometry.Cantor.BidirectionalChiralRandomWalk

/-- Canonical projection capstone for Bidirectional Chiral Cantor Random Walk module. -/
theorem bidirectional_chiral_random_walk_canonical_capstone
    {n : ℕ} (state : BiCantorState n)
    (h_symm : state.left = state.right) (σ : ℝ) (h_balance : σ - 1 / 2 = 0) :
    (paritySwap (paritySwap state) = state) ∧
    (chiralCharge (paritySwap state) = - chiralCharge state) ∧
    (chiralCharge state = 0) ∧
    (numberL state = numberR state) ∧
    (σ = 1 / 2) :=
  grand_bidirectional_chiral_synthesis state h_symm σ h_balance

end InfoGeometry.Canonical
