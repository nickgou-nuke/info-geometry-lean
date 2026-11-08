/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.BostConnesAsymptoticLegendreDuality
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Bost-Connes Asymptotic Legendre Duality Capstone (Canonical Export)

Canonical umbrella export of the asymptotic Legendre duality for the Bost-Connes critical boundary.
-/

namespace InfoGeometry.Canonical.BostConnesAsymptotic

open InfoGeometry.Quantum.BostConnes
open InfoGeometry.Canonical.YangBaxterProof

/-- 🏆 Canonical Grand Synthesis of Asymptotic Legendre Duality & Yang-Baxter Integrability -/
theorem grand_canonical_bost_connes_asymptotic_synthesis (eta : ℝ) (h_eta : 0 < eta) :
    (dPhiAsymptotic eta = - betaAsymptotic eta) ∧
    (0 < dualHessianAsymptotic eta) ∧
    (phiAsymptotic eta - eta * dPhiAsymptotic eta = - Real.log eta) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨dphi_eq_neg_beta eta,
   dual_hessian_pos eta h_eta,
   legendre_fenchel_identity eta h_eta,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.BostConnesAsymptotic

