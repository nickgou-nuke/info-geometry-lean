/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Topological.VerlindeDefectFusion

namespace InfoGeometry.Canonical

open InfoGeometry.Topological.VerlindeDefectFusion

/-- Canonical projection capstone for Verlinde Defect Fusion module. -/
theorem verlinde_defect_fusion_canonical_capstone
    (p q γ : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (verlindeSMatrix2 * verlindeSMatrix2.transpose = 1) ∧
    (totalQuantumDimensionSq = 2) ∧
    (‖primeDefectLineAction p γ‖ = 1) ∧
    (primeDefectFusion p q γ = primeDefectLineAction (p * q) γ) ∧
    (primeDefectLineAction p γ * primeDefectLineAction q γ -
     primeDefectLineAction q γ * primeDefectLineAction p γ = 0) :=
  grand_verlinde_defect_fusion_synthesis p q γ hp hq

end InfoGeometry.Canonical
