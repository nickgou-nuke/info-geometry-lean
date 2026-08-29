/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Conformal.SchwarzianApollonius

namespace InfoGeometry.Canonical

open InfoGeometry.Conformal.SchwarzianApollonius Complex

/-- 🏆 GRAND CANONICAL CAPSTONE: Apollonius Schwarzian Derivative & Zero CFT Anomaly Synthesis -/
theorem grand_canonical_apollonius_schwarzian_synthesis
    (s : ℂ) (hs : s + (1 / 2 : ℂ) ≠ 0) (c : ℂ) :
    (apolloniusDeriv2 s / apolloniusDeriv1 s = apolloniusAffineConnection s) ∧
    ((2 : ℂ) / (s + (1 / 2 : ℂ)) ^ 2 - (1 / 2 : ℂ) * (apolloniusAffineConnection s) ^ 2 = 0) ∧
    (- (c / 12) * ((2 : ℂ) / (s + (1 / 2 : ℂ)) ^ 2 - (1 / 2 : ℂ) * (apolloniusAffineConnection s) ^ 2) = 0) :=
  grand_apollonius_schwarzian_synthesis s hs c

end InfoGeometry.Canonical
