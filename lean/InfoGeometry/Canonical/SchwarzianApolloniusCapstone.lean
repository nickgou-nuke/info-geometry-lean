/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Conformal.SchwarzianApollonius
import InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Canonical.SchwarzianApolloniusCapstone

open Complex Matrix
open InfoGeometry.Conformal.SchwarzianApollonius
open InfoGeometry.Canonical.YangBaxterProof

noncomputable section

/-- 🏆 GRAND CAPSTONE: Schwarzian Invariance, Zero CFT Central Anomaly & Quantum Yang-Baxter Synthesis -/
theorem grand_apollonius_schwarzian_capstone
    (s : ℂ) (hs : s + (1 / 2 : ℂ) ≠ 0) (c : ℂ) :
    (apolloniusDeriv2 s / apolloniusDeriv1 s = apolloniusAffineConnection s) ∧
    ((2 : ℂ) / (s + (1 / 2 : ℂ)) ^ 2 - (1 / 2 : ℂ) * (apolloniusAffineConnection s) ^ 2 = 0) ∧
    (- (c / 12) * ((2 : ℂ) / (s + (1 / 2 : ℂ)) ^ 2 - (1 / 2 : ℂ) * (apolloniusAffineConnection s) ^ 2) = 0) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨(grand_apollonius_schwarzian_synthesis s hs c).1,
   (grand_apollonius_schwarzian_synthesis s hs c).2.1,
   (grand_apollonius_schwarzian_synthesis s hs c).2.2,
   F_sq,
   F_B_F_eq_R⟩

end

end InfoGeometry.Canonical.SchwarzianApolloniusCapstone
