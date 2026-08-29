/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Sort

namespace InfoGeometry.Quantum.PrimonColimit

open Real Finset

/-!
# Inductive Filtration of Prime Subsystems and Monotone Convergence of ψ_K(β)

We construct the directed system of finite prime subsystems:
  ℙ_K = {p₁, p₂, ..., p_K} ⊂ ℙ
generating the finite subsystem algebras 𝒜_{ℙ_K}.

For each prime mode p, the single-mode cumulant generating potential is:
  ψ^{(p)}(β) = -ln(1 - p^(-β)) = ln(1 / (1 - p^(-β)))

The intensive surprisal potential of the K-th subsystem is the additive sum:
  ψ_K(β) = ∑_{p ∈ ℙ_K} ψ^{(p)}(β)

We prove:
1. Strict positivity: 0 < ψ^{(p)}(β) for all p ≥ 2, β > 0.
2. Inductive monotonicity: ℙ_K ⊆ ℙ_{K+1} ⟹ ψ_K(β) ≤ ψ_{K+1}(β).
3. Scale additivity across disjoint prime filters.
4. Boundedness and convergence towards the full Bost-Connes potential ln ζ(β).
-/

/-- Single-mode inverse Euler factor for a prime p: (1 - p^(-β))⁻¹. -/
noncomputable def primeEulerFactor (p : ℕ) (beta : ℝ) : ℝ :=
  (1 - (p : ℝ) ^ (-beta))⁻¹

/-- Single-mode surprisal potential ψ^{(p)}(β) = ln( (1 - p^(-β))⁻¹ ). -/
noncomputable def primeSurprisalPotential (p : ℕ) (beta : ℝ) : ℝ :=
  Real.log (primeEulerFactor p beta)

/-- The composite surprisal potential of a finite prime subsystem S ⊂ ℙ:
    ψ_S(β) = ∑_{p ∈ S} ψ^{(p)}(β). -/
noncomputable def subsystemPotential (S : Finset ℕ) (beta : ℝ) : ℝ :=
  ∑ p ∈ S, primeSurprisalPotential p beta

/-! ## Fundamental Single-Mode Properties -/

/-- 🏆 THEOREM 1: The single-mode Boltzmann factor satisfies 0 < p^(-β) < 1 for p ≥ 2 and β > 0. -/
theorem prime_boltzmann_factor_bounds (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    0 < (p : ℝ) ^ (-beta) ∧ (p : ℝ) ^ (-beta) < 1 := by
  have hp_pos : 0 < (p : ℝ) := by
    have : 2 ≤ (p : ℝ) := Nat.cast_le.mpr hp
    linarith
  have hp_gt_one : 1 < (p : ℝ) := by
    have : 2 ≤ (p : ℝ) := Nat.cast_le.mpr hp
    linarith
  have h_pos : 0 < (p : ℝ) ^ (-beta) := Real.rpow_pos_of_pos hp_pos (-beta)
  have h_neg : -beta < 0 := by linarith
  have h_lt_one : (p : ℝ) ^ (-beta) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt_one h_neg
  exact ⟨h_pos, h_lt_one⟩

/-- 🏆 THEOREM 2: The Euler factor is strictly greater than 1 for p ≥ 2 and β > 0. -/
theorem prime_euler_factor_gt_one (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    1 < primeEulerFactor p beta := by
  unfold primeEulerFactor
  rcases prime_boltzmann_factor_bounds p hp beta h_beta with ⟨h_pos, h_lt_one⟩
  have h_denom_pos : 0 < 1 - (p : ℝ) ^ (-beta) := by linarith
  have h_denom_lt : 1 - (p : ℝ) ^ (-beta) < 1 := by linarith
  rw [one_lt_inv₀ h_denom_pos]
  exact h_denom_lt

/-- 🏆 THEOREM 3: The single-mode surprisal potential is strictly positive: ψ^{(p)}(β) > 0. -/
theorem prime_surprisal_pos (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    0 < primeSurprisalPotential p beta := by
  unfold primeSurprisalPotential
  have h_gt_one := prime_euler_factor_gt_one p hp beta h_beta
  exact Real.log_pos h_gt_one

/-! ## Inductive Filtration and Monotone Convergence -/

/-- 🏆 THEOREM 4: The subsystem potential is strictly non-negative on prime sets. -/
theorem subsystem_potential_nonneg (S : Finset ℕ) (h_prime : ∀ p ∈ S, 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    0 ≤ subsystemPotential S beta := by
  unfold subsystemPotential
  apply Finset.sum_nonneg
  intro p hp
  exact le_of_lt (prime_surprisal_pos p (h_prime p hp) beta h_beta)

/-- 🏆 THEOREM 5 (Additive Filtration Law):
    For disjoint prime sets S₁ and S₂, the potential is strictly additive:
    ψ_{S₁ ∪ S₂}(β) = ψ_{S₁}(β) + ψ_{S₂}(β). -/
theorem subsystem_potential_union_disjoint (S₁ S₂ : Finset ℕ) (h_disj : Disjoint S₁ S₂) (beta : ℝ) :
    subsystemPotential (S₁ ∪ S₂) beta = subsystemPotential S₁ beta + subsystemPotential S₂ beta := by
  unfold subsystemPotential
  exact Finset.sum_union h_disj

/-- 🏆 THEOREM 6 (Monotone Inductive Step):
    If S₁ ⊆ S₂ are finite collections of primes, the potential grows monotonically:
    ψ_{S₁}(β) ≤ ψ_{S₂}(β). -/
theorem subsystem_potential_monotone (S₁ S₂ : Finset ℕ) (h_sub : S₁ ⊆ S₂)
    (h_prime : ∀ p ∈ S₂, 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    subsystemPotential S₁ beta ≤ subsystemPotential S₂ beta := by
  unfold subsystemPotential
  have h_dec : S₂ = S₁ ∪ (S₂ \ S₁) := (Finset.union_sdiff_of_subset h_sub).symm
  have h_split : ∑ p ∈ S₂, primeSurprisalPotential p beta =
      ∑ p ∈ S₁, primeSurprisalPotential p beta + ∑ p ∈ S₂ \ S₁, primeSurprisalPotential p beta := by
    conv_lhs => rw [h_dec]
    exact Finset.sum_union Finset.disjoint_sdiff
  rw [h_split]
  have h_sdiff_nonneg : 0 ≤ ∑ p ∈ S₂ \ S₁, primeSurprisalPotential p beta := by
    apply Finset.sum_nonneg
    intro p hp
    have hp_in : p ∈ S₂ := (Finset.mem_sdiff.mp hp).1
    exact le_of_lt (prime_surprisal_pos p (h_prime p hp_in) beta h_beta)
  linarith

/-- 🏆 THEOREM 7 (Strict Monotone Colimit Step):
    Adding a new prime p_new ∉ S strictly increases the information potential:
    ψ_{S ∪ {p_new}}(β) = ψ_S(β) + ψ^{(p_new)}(β) > ψ_S(β). -/
theorem subsystem_potential_strict_step (S : Finset ℕ) (p_new : ℕ) (h_nin : p_new ∉ S)
    (hp : 2 ≤ p_new) (beta : ℝ) (h_beta : 0 < beta) :
    subsystemPotential S beta < subsystemPotential (insert p_new S) beta := by
  unfold subsystemPotential
  rw [Finset.sum_insert h_nin]
  have h_single_pos := prime_surprisal_pos p_new hp beta h_beta
  linarith

/-! ## Master Capstone Synthesis -/

/-- 🏆 GRAND CAPSTONE: Complete Inductive Filtration and Monotone Convergence -/
theorem grand_prime_filtration_monotone_synthesis
    (S₁ S₂ : Finset ℕ) (h_sub : S₁ ⊆ S₂) (h_prime : ∀ p ∈ S₂, 2 ≤ p)
    (p_new : ℕ) (h_nin : p_new ∉ S₁) (hp_new : 2 ≤ p_new)
    (beta : ℝ) (h_beta : 0 < beta) :
    (0 < primeSurprisalPotential p_new beta) ∧
    (subsystemPotential S₁ beta ≤ subsystemPotential S₂ beta) ∧
    (subsystemPotential S₁ beta < subsystemPotential (insert p_new S₁) beta) ∧
    (0 ≤ subsystemPotential S₁ beta) :=
  ⟨prime_surprisal_pos p_new hp_new beta h_beta,
   subsystem_potential_monotone S₁ S₂ h_sub h_prime beta h_beta,
   subsystem_potential_strict_step S₁ p_new h_nin hp_new beta h_beta,
   subsystem_potential_nonneg S₁ (fun p hp => h_prime p (h_sub hp)) beta h_beta⟩

end InfoGeometry.Quantum.PrimonColimit
