/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
4. Log-Product morphism and first-order Taylor lower bound.
5. Exact Mercator harmonic series expansion ψ^{(p)}(β) = ∑_{k=0}^∞ (p^(-β))^(k+1)/(k+1).
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

/-! ## Log-Product Morphism & Taylor Lower Bound -/

/-- 🏆 THEOREM 8 (Log-Product Morphism):
    The composite potential ψ_S(β) equals the log of the finite Euler product:
    ψ_S(β) = ln( ∏_{p ∈ S} (1 - p^(-β))⁻¹ ). -/
theorem subsystem_potential_eq_log_prod (S : Finset ℕ) (h_prime : ∀ p ∈ S, 2 ≤ p)
    (beta : ℝ) (h_beta : 0 < beta) :
    subsystemPotential S beta = Real.log (∏ p ∈ S, primeEulerFactor p beta) := by
  unfold subsystemPotential primeSurprisalPotential
  rw [Real.log_prod]
  intro p hp
  have h_gt := prime_euler_factor_gt_one p (h_prime p hp) beta h_beta
  linarith

/-- 🏆 THEOREM 9 (Finite Euler Product Lower Bound):
    ∏_{p ∈ S} (1 - p^(-β))⁻¹ ≥ 1 for any prime subset S. -/
theorem finite_euler_prod_ge_one (S : Finset ℕ) (h_prime : ∀ p ∈ S, 2 ≤ p)
    (beta : ℝ) (h_beta : 0 < beta) :
    1 ≤ ∏ p ∈ S, primeEulerFactor p beta := by
  have h_log_nonneg : 0 ≤ Real.log (∏ p ∈ S, primeEulerFactor p beta) := by
    rw [← subsystem_potential_eq_log_prod S h_prime beta h_beta]
    exact subsystem_potential_nonneg S h_prime beta h_beta
  have h_pos : 0 < ∏ p ∈ S, primeEulerFactor p beta := by
    apply Finset.prod_pos
    intro p hp
    have h_gt := prime_euler_factor_gt_one p (h_prime p hp) beta h_beta
    linarith
  rw [← Real.log_one] at h_log_nonneg
  exact (Real.log_le_log_iff (by positivity) h_pos).mp h_log_nonneg

/-- 🏆 THEOREM 10 (First-Order Taylor Lower Bound):
    p^(-β) ≤ ψ^{(p)}(β) for all p ≥ 2 and β > 0. -/
theorem prime_surprisal_ge_linear (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    (p : ℝ) ^ (-beta) ≤ primeSurprisalPotential p beta := by
  rcases prime_boltzmann_factor_bounds p hp beta h_beta with ⟨h_pos, h_lt_one⟩
  unfold primeSurprisalPotential primeEulerFactor
  have h_denom : 0 < 1 - (p : ℝ) ^ (-beta) := by linarith
  rw [Real.log_inv]
  have h_log_le : Real.log (1 - (p : ℝ) ^ (-beta)) ≤ - ((p : ℝ) ^ (-beta)) := by
    have h_le := Real.log_le_sub_one_of_pos h_denom
    linarith
  linarith

/-! ## Mercator Series Expansion of Single-Mode Potentials -/

/-- 🏆 THEOREM 11 (Mercator Series Representation of Single-Mode Potential):
    ψ^{(p)}(β) = ∑_{k=0}^∞ (p^(-β))^(k+1) / (k+1) = ∑_{k=1}^∞ (p^(-β))^k / k. -/
theorem hasSum_prime_surprisal_series (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    HasSum (fun k : ℕ => ((p : ℝ) ^ (-beta)) ^ (k + 1) / ((k : ℝ) + 1)) (primeSurprisalPotential p beta) := by
  rcases prime_boltzmann_factor_bounds p hp beta h_beta with ⟨h_pos, h_lt_one⟩
  have h_abs : |(p : ℝ) ^ (-beta)| < 1 := by
    rw [abs_of_pos h_pos]
    exact h_lt_one
  have h_sum := hasSum_pow_div_log_of_abs_lt_one h_abs
  unfold primeSurprisalPotential primeEulerFactor
  rw [Real.log_inv]
  exact h_sum

/-- 🏆 THEOREM 12 (Summability of the Primon Excitation Series):
    The excitation series is summable for every prime p ≥ 2 and β > 0. -/
theorem summable_prime_surprisal_series (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    Summable (fun k : ℕ => ((p : ℝ) ^ (-beta)) ^ (k + 1) / ((k : ℝ) + 1)) :=
  (hasSum_prime_surprisal_series p hp beta h_beta).summable

end InfoGeometry.Quantum.PrimonColimit
