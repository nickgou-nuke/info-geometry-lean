/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.DikinApolloniusTrap

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.DikinApolloniusTrap Real

/-- 🏆 GRAND CANONICAL CAPSTONE: Dikin Ellipsoid Lyapunov Trap Synthesis -/
theorem grand_canonical_dikin_apollonius_trap_synthesis
    (ξ r : ℝ) :
    (dikinScaleBarrier ξ = 2 * Real.log (Real.cosh ξ)) ∧
    (0 < dikinScaleMetric ξ) ∧
    (dikinScaleMetric 0 = 2) ∧
    (∀ y Ty Kc, 0 ≤ Kc → y ∈ dikinEquilibriumEllipsoid r → |Ty| ≤ Kc * |y| →
      2 * Ty ^ 2 ≤ (Kc * r) ^ 2) :=
  grand_dikin_apollonius_trap_synthesis ξ r

end InfoGeometry.Canonical
