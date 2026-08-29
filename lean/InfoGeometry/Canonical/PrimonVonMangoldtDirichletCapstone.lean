/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Quantum.PrimonSeriesVonMangoldt
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Primon Von Mangoldt Dirichlet Capstone (Canonical Export)

Canonical umbrella export of the exchange of the double sum over primon modes
with the von Mangoldt log-weighted Dirichlet series.
-/

namespace InfoGeometry.Canonical.PrimonVonMangoldt

open InfoGeometry.Quantum.PrimonSeries
open InfoGeometry.Canonical.YangBaxterProof

/-- 🏆 Canonical Grand Synthesis of Primon von Mangoldt Dirichlet Exchange & Yang-Baxter Integrability -/
theorem grand_canonical_primon_vonMangoldt_synthesis
    (p : PrimeNat) (beta : ℝ) (k : ℕ) :
    (((p : ℝ) ^ (-beta)) ^ (k + 1) = (p : ℝ) ^ (-(k + 1 : ℝ) * beta)) ∧
    (primonDoubleTerm beta ⟨p, k⟩ = vonMangoldtDirichletTerm beta (primePowerEquiv ⟨p, k⟩)) ∧
    (2 ≤ primePowerEquiv ⟨p, k⟩) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨primon_power_law (p : ℕ) p.2.two_le beta k,
   primon_term_eq_vonMangoldt_term beta ⟨p, k⟩,
   primePower_ge_two ⟨p, k⟩,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.PrimonVonMangoldt
