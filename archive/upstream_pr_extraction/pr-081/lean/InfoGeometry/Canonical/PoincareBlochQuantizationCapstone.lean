/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.PoincareBlochQuantization

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.PoincareBlochQuantization

/-- Canonical projection capstone for Poincaré/Bloch Quantization module. -/
theorem poincare_bloch_quantization_canonical_capstone (σ : ℝ)
    (h_balanced : Real.exp (2 * (σ - 1 / 2)) = 1) :
    (vacuumZeroPointEnergy = 1 / 2) ∧
    (σ = 1 / 2) :=
  grand_poincare_bloch_synthesis σ h_balanced

end InfoGeometry.Canonical
