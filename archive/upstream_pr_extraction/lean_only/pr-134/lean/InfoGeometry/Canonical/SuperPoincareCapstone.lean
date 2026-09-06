/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.SuperPoincare

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.SuperPoincare

/-- Canonical projection capstone for Super-Poincaré Wigner classification module. -/
theorem super_poincare_canonical_capstone
    (σ J ξ : ℝ)
    (h_bps_xi : IsBPS_ShortMultiplet J ξ)
    (h_bps_sigma : IsBPS_ShortMultiplet J (σ - 1 / 2)) :
    (ξ = 0) ∧ (σ = 1 / 2) :=
  grand_super_poincare_synthesis σ J ξ h_bps_xi h_bps_sigma

end InfoGeometry.Canonical
