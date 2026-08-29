/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.ModularSurprisalDeficit

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.ModularSurprisalDeficit Real

/-- 🏆 GRAND CANONICAL CAPSTONE: Modular Surprisal Deficit & Operator Convexity Synthesis -/
theorem grand_canonical_surprisal_deficit_synthesis (x : ℝ) :
    (surprisalDeficit 0 = 0) ∧
    (0 ≤ surprisalDeficit x) ∧
    (HasDerivAt surprisalDeficit 0 0) :=
  grand_surprisal_deficit_synthesis x

end InfoGeometry.Canonical
