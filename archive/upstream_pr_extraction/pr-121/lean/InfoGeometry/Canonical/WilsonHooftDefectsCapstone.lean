/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Topological.WilsonHooftDefects

namespace InfoGeometry.Canonical

open InfoGeometry.Topological.WilsonHooftDefects

/-- Canonical projection capstone for Wilson and 't Hooft Defects module. -/
theorem wilson_hooft_defects_canonical_capstone
    (p q γ k : ℝ) (n : ℤ) (hk : k ≠ 0) :
    (wilsonLoopDefect p 0 = 2) ∧
    (wilsonLoopDefect p (-γ) = wilsonLoopDefect p γ) ∧
    (‖tHooftDefectOperator 1 γ‖ = 1) ∧
    (topologicalLinkingPhase k (k * (n : ℝ)) = 1) ∧
    (wilsonLoopDefect p γ * wilsonLoopDefect q γ -
     wilsonLoopDefect q γ * wilsonLoopDefect p γ = 0) :=
  grand_wilson_hooft_defects_synthesis p q γ k n hk

end InfoGeometry.Canonical
