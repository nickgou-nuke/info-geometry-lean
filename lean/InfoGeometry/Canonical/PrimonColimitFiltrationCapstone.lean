/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Quantum.PrimonColimitFiltration
import InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Canonical.PrimonColimit

open InfoGeometry.Quantum.PrimonColimit
open InfoGeometry.Canonical.YangBaxterProof

/-- Canonical synthesis of finite primon filtration and Yang--Baxter laws. -/
theorem grand_canonical_primon_colimit_synthesis
    (S₁ S₂ : Finset ℕ) (h_sub : S₁ ⊆ S₂) (h_prime : ∀ p ∈ S₂, 2 ≤ p)
    (p_new : ℕ) (h_nin : p_new ∉ S₁) (hp_new : 2 ≤ p_new)
    (beta : ℝ) (h_beta : 0 < beta) :
    (0 < primeSurprisalPotential p_new beta) ∧
    (subsystemPotential S₁ beta ≤ subsystemPotential S₂ beta) ∧
    (subsystemPotential S₁ beta < subsystemPotential (insert p_new S₁) beta) ∧
    (0 ≤ subsystemPotential S₁ beta) ∧
    (subsystemPotential S₁ beta = Real.log (∏ p ∈ S₁, primeEulerFactor p beta)) ∧
    (1 ≤ ∏ p ∈ S₁, primeEulerFactor p beta) ∧
    ((p_new : ℝ) ^ (-beta) ≤ primeSurprisalPotential p_new beta) ∧
    (HasSum (fun k : ℕ => ((p_new : ℝ) ^ (-beta)) ^ (k + 1) / ((k : ℝ) + 1))
      (primeSurprisalPotential p_new beta)) ∧
    (Summable (fun k : ℕ => ((p_new : ℝ) ^ (-beta)) ^ (k + 1) / ((k : ℝ) + 1))) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨prime_surprisal_pos p_new hp_new beta h_beta,
   subsystem_potential_monotone S₁ S₂ h_sub h_prime beta h_beta,
   subsystem_potential_strict_step S₁ p_new h_nin hp_new beta h_beta,
   subsystem_potential_nonneg S₁ (fun p hp => h_prime p (h_sub hp)) beta h_beta,
   subsystem_potential_eq_log_prod S₁ (fun p hp => h_prime p (h_sub hp)) beta h_beta,
   finite_euler_prod_ge_one S₁ (fun p hp => h_prime p (h_sub hp)) beta h_beta,
   prime_surprisal_ge_linear p_new hp_new beta h_beta,
   hasSum_prime_surprisal_series p_new hp_new beta h_beta,
   summable_prime_surprisal_series p_new hp_new beta h_beta,
   F_sq, F_B_F_eq_R⟩

end InfoGeometry.Canonical.PrimonColimit
