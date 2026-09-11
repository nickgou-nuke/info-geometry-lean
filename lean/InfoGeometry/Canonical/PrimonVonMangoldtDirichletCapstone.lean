/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.PrimonSeriesVonMangoldt
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Canonical.PrimonVonMangoldtDirichlet

open InfoGeometry.Quantum.PrimonSeries
open InfoGeometry.Canonical.YangBaxterProof

/-- Canonical synthesis of primon power scaling and von Mangoldt alignment. -/
theorem grand_primon_double_sum_exchange_synthesis
    (p : PrimeNat) (beta : ℝ) (k : ℕ) :
    (((p : ℝ) ^ (-beta)) ^ (k + 1) = (p : ℝ) ^ (-(k + 1 : ℝ) * beta)) ∧
    (2 ≤ primePowerEquiv ⟨p, k⟩) ∧
    (primonDoubleTerm beta ⟨p, k⟩ = vonMangoldtDirichletTerm beta (primePowerEquiv ⟨p, k⟩)) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨primon_power_law (p : ℕ) p.2.two_le beta k,
   primePower_ge_two ⟨p, k⟩,
   primon_term_eq_vonMangoldt_term beta ⟨p, k⟩,
   F_sq, F_B_F_eq_R⟩

end InfoGeometry.Canonical.PrimonVonMangoldtDirichlet
