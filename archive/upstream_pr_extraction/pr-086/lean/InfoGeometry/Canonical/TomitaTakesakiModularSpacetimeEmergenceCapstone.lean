/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.TomitaTakesakiModularSpacetimeEmergence

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.TomitaTakesakiModularSpacetimeEmergence

/-- Canonical projection capstone for Tomita-Takesaki Modular Spacetime Emergence module. -/
theorem tomita_takesaki_modular_spacetime_emergence_canonical_capstone
    (pair : ℝ × ℝ) (h_eq : pair.1 = pair.2)
    (σ : ℝ) (h_casimir : σ - 1 / 2 = 0) :
    (modularConjugation (modularConjugation pair) = pair) ∧
    (modularRapidity (modularConjugation pair) = - modularRapidity pair) ∧
    (modularRapidity pair = 0) ∧
    (σ = 1 / 2) :=
  grand_tomita_spacetime_synthesis pair h_eq σ h_casimir

end InfoGeometry.Canonical
