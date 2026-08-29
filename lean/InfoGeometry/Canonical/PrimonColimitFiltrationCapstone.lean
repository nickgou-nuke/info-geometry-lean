/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Quantum.PrimonColimitFiltration
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Primon Colimit Filtration Capstone (Canonical Export)

Canonical umbrella export of the inductive filtration of prime subsystems and monotone convergence of surprisal potentials.
-/

namespace InfoGeometry.Canonical.PrimonColimit

open InfoGeometry.Quantum.PrimonColimit
open InfoGeometry.Canonical.YangBaxterProof

/-- 🏆 Canonical Grand Synthesis of Primon Inductive Filtration & Yang-Baxter Integrability -/
theorem grand_canonical_primon_colimit_synthesis
    (S₁ S₂ : Finset ℕ) (h_sub : S₁ ⊆ S₂) (h_prime : ∀ p ∈ S₂, 2 ≤ p)
    (p_new : ℕ) (h_nin : p_new ∉ S₁) (hp_new : 2 ≤ p_new)
    (beta : ℝ) (h_beta : 0 < beta) :
    (0 < primeSurprisalPotential p_new beta) ∧
    (subsystemPotential S₁ beta ≤ subsystemPotential S₂ beta) ∧
    (subsystemPotential S₁ beta < subsystemPotential (insert p_new S₁) beta) ∧
    (0 ≤ subsystemPotential S₁ beta) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨prime_surprisal_pos p_new hp_new beta h_beta,
   subsystem_potential_monotone S₁ S₂ h_sub h_prime beta h_beta,
   subsystem_potential_strict_step S₁ p_new h_nin hp_new beta h_beta,
   subsystem_potential_nonneg S₁ (fun p hp => h_prime p (h_sub hp)) beta h_beta,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.PrimonColimit
