/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.MontgomeryDysonG2Bridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.MontgomeryDysonG2Capstone

open InfoGeometry.Canonical.MontgomeryDysonG2

/-- Canonical projection of the finite Montgomery--Dyson `G₂` certificate. -/
theorem montgomery_dyson_g2_canonical_capstone
    (s : ℝ) (hs : s ^ 2 ≤ 1) (hs_nonneg : 0 ≤ s ^ 2) :
    (montgomeryDysonCorrelation 1 = 0) ∧
    (montgomeryDysonCorrelation 0 = 1) ∧
    (0 ≤ montgomeryDysonCorrelation s ∧ montgomeryDysonCorrelation s ≤ 1) ∧
    (g2TotalFlags = 189 ∧ g2BruhatCells = 12) :=
  grand_montgomery_dyson_g2_synthesis s hs hs_nonneg

end InfoGeometry.Canonical.MontgomeryDysonG2Capstone
