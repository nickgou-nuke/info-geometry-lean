/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.LightCone.ChiralPrimeDecomposition

namespace InfoGeometry.Canonical

open InfoGeometry.LightCone.ChiralPrimeDecomposition Complex Real

/-- 🏆 GRAND CANONICAL CAPSTONE: Chiral Prime Left- and Right-Moving Decomposition -/
theorem grand_canonical_chiral_prime_decomposition_synthesis
    (p k_L k_R m n : ℝ) (hm : 0 < m) (hn : 0 < n) :
    (let d_u := ((1 : ℝ) + 1) / 2; let d_v := ((1 : ℝ) - 1) / 2; d_u - d_v = 1) ∧
    (‖chiralLeftPrimePhase p k_L‖ = 1) ∧
    (‖chiralRightPrimePhase p k_R‖ = 1) ∧
    (fullPrimePhase p k_L k_R = chiralLeftPrimePhase p k_L * (chiralRightPrimePhase p k_R)⁻¹) ∧
    (chiralLeftPrimePhase (m * n) k_L = chiralLeftPrimePhase m k_L * chiralLeftPrimePhase n k_L) ∧
    (chiralRightPrimePhase (m * n) k_R = chiralRightPrimePhase m k_R * chiralRightPrimePhase n k_R) :=
  grand_chiral_prime_decomposition_synthesis p k_L k_R m n hm hn

end InfoGeometry.Canonical
