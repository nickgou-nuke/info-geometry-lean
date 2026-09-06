/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.ChiralParityCharge

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.ChiralParityCharge

/-- Canonical projection capstone for Chiral Parity Charge module. -/
theorem chiral_parity_charge_canonical_capstone {R : Type*} [CommRing R]
    (N_L N_R : R) (σ : ℝ)
    (h_eq : N_L = N_R) (h_chiral : chiralParityCharge σ (1 / 2) = 0) :
    (chiralParityCharge N_R N_L = - chiralParityCharge N_L N_R) ∧
    (chiralParityCharge N_L N_R = 0) ∧
    (σ = 1 / 2) :=
  grand_chiral_parity_synthesis N_L N_R σ h_eq h_chiral

end InfoGeometry.Canonical
