/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.PoincareBlochQuantization

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.PoincareBlochQuantization

/-- Canonical projection of the balanced Poincaré/Bloch condition. -/
theorem poincare_bloch_quantization_canonical_capstone (σ : ℝ)
    (h_balanced : Real.exp (2 * (σ - 1 / 2)) = 1) :
    (vacuumZeroPointEnergy = 1 / 2) ∧
    (σ = 1 / 2) := by
  exact ⟨berry_keating_ground_state_energy,
    poincare_equator_confinement σ h_balanced⟩

end InfoGeometry.Canonical
