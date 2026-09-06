/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.ChiralCantorLandauerReversibility

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.ChiralCantorLandauerReversibility

/-- Canonical projection capstone for Chiral Cantor Landauer Reversibility module. -/
theorem chiral_cantor_landauer_reversibility_canonical_capstone
    (k T σ : ℝ) (hk : 0 < k) (hT : 0 < T)
    (h_casimir : σ - 1 / 2 = 0) :
    (0 < landauerDissipatedHeat k T) ∧
    (landauerDissipatedHeat 0 T = 0) ∧
    (σ = 1 / 2) :=
  grand_chiral_landauer_synthesis k T σ hk hT h_casimir

end InfoGeometry.Canonical
