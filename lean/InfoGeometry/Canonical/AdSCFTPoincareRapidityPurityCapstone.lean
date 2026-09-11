/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.AdSCFTPoincareRapidityPurity
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.AdSCFTPoincareRapidityPurity

/-- Canonical projection capstone for Arithmetic AdS/CFT Rapidity & Quantum Purity module. -/
theorem adscft_poincare_rapidity_purity_canonical_capstone
    (p q σ : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h_pure : quantumPurity σ = 1) :
    (rapidityBoost (p * q) = rapidityBoost p + rapidityBoost q) ∧
    (quantumPurity σ ≤ 1) ∧
    (quantumPurity (1 / 2) = 1) ∧
    (σ = 1 / 2) :=
  ⟨rapidity_boost_additivity p q hp hq,
   quantum_purity_le_one σ,
   critical_line_purity,
   pure_state_confinement σ h_pure⟩

end InfoGeometry.Canonical
