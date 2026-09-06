/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.BostConnesPrimonGas

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.BostConnesPrimonGas Finset Real

/-- 🏆 GRAND CANONICAL CAPSTONE: Bost-Connes Primon Gas Möbius KMS Synthesis -/
theorem grand_canonical_bost_connes_moebius_kms_synthesis
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ) (hβ : 1 < β) (S : Finset ℕ) (hS : ∀ q ∈ S, 2 ≤ q) :
    (bosonicFactor p β * fermionicFactor p β = 1) ∧
    ((∏ q ∈ S, bosonicFactor q β) * (∏ q ∈ S, fermionicFactor q β) = 1) ∧
    (0 < fermionicFactor p β ∧ fermionicFactor p β < 1) ∧
    (0 < Real.log (p : ℝ)) ∧
    ((p : ℝ) ^ (-β) = Real.exp (-β * Real.log (p : ℝ))) :=
  grand_bost_connes_moebius_kms_synthesis p hp β hβ S hS

end InfoGeometry.Canonical
