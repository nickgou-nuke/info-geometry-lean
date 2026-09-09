/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Cantor.BidirectionalChiralRandomWalk

namespace InfoGeometry.Canonical

open InfoGeometry.Cantor.BidirectionalChiralRandomWalk

theorem bidirectional_chiral_random_walk_canonical_capstone
    {n : ℕ} (state : BiCantorState n)
    (h_symm : state.left = state.right) (σ : ℝ)
    (h_balance : σ - 1 / 2 = 0) :
    (paritySwap (paritySwap state) = state) ∧
    (chiralCharge (paritySwap state) = - chiralCharge state) ∧
    (chiralCharge state = 0) ∧
    (numberL state = numberR state) ∧
    (σ = 1 / 2) := by
  exact ⟨parity_swap_involutive state,
    chiral_charge_parity_odd state,
    chiral_charge_symmetric_zero state h_symm,
    equal_populations_of_zero_charge state
      (chiral_charge_symmetric_zero state h_symm),
    critical_line_from_bidirectional_balance σ h_balance⟩

end InfoGeometry.Canonical
