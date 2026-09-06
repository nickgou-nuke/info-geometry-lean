/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.BostConnesPrimonGas

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.BostConnesPrimonGas Finset Real

theorem grand_canonical_bost_connes_moebius_kms_synthesis
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ) (hβ : 1 < β) (S : Finset ℕ)
    (hS : ∀ q ∈ S, 2 ≤ q) :
    (bosonicFactor p β * fermionicFactor p β = 1) ∧
    ((∏ q ∈ S, bosonicFactor q β) * (∏ q ∈ S, fermionicFactor q β) = 1) ∧
    (0 < fermionicFactor p β ∧ fermionicFactor p β < 1) ∧
    (0 < Real.log (p : ℝ)) ∧
    ((p : ℝ) ^ (-β) = Real.exp (-β * Real.log (p : ℝ))) := by
  exact ⟨bosonic_fermionic_factor_duality p hp β (by linarith),
    finite_primon_gas_duality S hS β (by linarith),
    fermionic_factor_bounds p hp β hβ,
    primon_energy_pos p hp,
    boltzmann_weight_eq_exp_neg_beta_log p hp β⟩

end InfoGeometry.Canonical
