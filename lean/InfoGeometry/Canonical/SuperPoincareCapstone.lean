/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.SuperPoincare
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.SuperPoincare

theorem super_poincare_canonical_capstone
    (σ J ξ : ℝ)
    (h_bps_xi : IsBPS_ShortMultiplet J ξ)
    (h_bps_sigma : IsBPS_ShortMultiplet J (σ - 1 / 2)) :
    (ξ = 0) ∧ (σ = 1 / 2) := by
  exact ⟨super_poincare_rapidity_collapse J ξ h_bps_xi,
    wigner_riemann_classification σ J h_bps_sigma⟩

end InfoGeometry.Canonical
