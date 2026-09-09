/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Topological.WilsonHooftDefects

namespace InfoGeometry.Canonical

open InfoGeometry.Topological.WilsonHooftDefects

/-- Canonical synthesis of the finite Wilson/'t Hooft defect laws. -/
theorem wilson_hooft_defects_canonical_capstone
    (p q γ k : ℝ) (n : ℤ) (hk : k ≠ 0) :
    (wilsonLoopDefect p 0 = 2) ∧
    (wilsonLoopDefect p (-γ) = wilsonLoopDefect p γ) ∧
    (‖tHooftDefectOperator 1 γ‖ = 1) ∧
    (topologicalLinkingPhase k (k * (n : ℝ)) = 1) ∧
    (wilsonLoopDefect p γ * wilsonLoopDefect q γ -
      wilsonLoopDefect q γ * wilsonLoopDefect p γ = 0) := by
  exact ⟨wilson_defect_vacuum p, wilson_defect_even p γ,
    t_hooft_defect_unitary 1 γ, topological_linking_quantization k n hk,
    wilson_defects_commute p q γ⟩

end InfoGeometry.Canonical
