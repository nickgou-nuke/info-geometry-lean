import Mathlib.Data.Nat.Choose.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Chebyshev Central Binomial Energy Bounds and Prime Product Dominance

This module formalizes:
1. The Chebyshev Central Binomial Upper Bound: (2n choose n) ≤ 4^n via the full binomial sum.
2. The Logarithmic Central Binomial Bound: log (2n choose n) ≤ n * log 4.
3. The Chebyshev θ(P) Prime Energy Sum: θ(P) = ∑_{p ∈ P} log p.
4. Strict positivity of prime logarithmic weights for p ≥ 2.
5. Logarithmic additivity of prime products: θ(P) = log (∏_{p ∈ P} p).
6. MASTER THEOREM 1 (Chebyshev Prime Interval Energy Bound):
     For any prime subset P whose product is bounded by the central binomial coefficient (2n choose n):
       θ(P) ≤ n * log 4.
7. MASTER THEOREM 2 (Chebyshev Prime Product Bounding Principle):
     For any finite set of primes P whose product is bounded by M:
       θ(P) ≤ log M.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.Arithmetic.Chebyshev

/-!
=============================================================================
PART 1: Central Binomial Combinatorial and Logarithmic Bounds
=============================================================================
-/

/-- THEOREM 1 (Central Binomial Upper Bound): (2n choose n) ≤ 4^n. -/
theorem choose_two_mul_le_four_pow (n : ℕ) :
    Nat.choose (2 * n) n ≤ 4 ^ n := by
  have h_sum : ∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k = 2 ^ (2 * n) :=
    Nat.sum_range_choose (2 * n)
  have h_mem : n ∈ Finset.range (2 * n + 1) := by
    rw [Finset.mem_range]
    have h_le : n ≤ 2 * n := by
      calc n = 1 * n := by rw [one_mul]
           _ ≤ 2 * n := Nat.mul_le_mul_right n (by decide : 1 ≤ 2)
    exact Nat.lt_succ_of_le h_le
  have h_single : Nat.choose (2 * n) n ≤ ∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) h_mem
  have h_four : 2 ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]
    rfl
  rw [h_sum, h_four] at h_single
  exact h_single

/-- THEOREM 2 (Logarithmic Central Binomial Chebyshev Bound): log (2n choose n) ≤ n * log 4. -/
theorem log_choose_two_mul_le_mul_log_four (n : ℕ) :
    Real.log (Nat.choose (2 * n) n : ℝ) ≤ (n : ℝ) * Real.log 4 := by
  have h_le := choose_two_mul_le_four_pow n
  have h_pos : 0 < (Nat.choose (2 * n) n : ℝ) := by
    have h_le_two : n ≤ 2 * n := by
      calc n = 1 * n := by rw [one_mul]
           _ ≤ 2 * n := Nat.mul_le_mul_right n (by decide : 1 ≤ 2)
    exact_mod_cast Nat.choose_pos h_le_two
  have h_cast : (Nat.choose (2 * n) n : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := by
    exact_mod_cast h_le
  have h_pow_cast : ((4 ^ n : ℕ) : ℝ) = (4 : ℝ) ^ n := by
    push_cast
    rfl
  rw [h_pow_cast] at h_cast
  have h_log := Real.log_le_log h_pos h_cast
  rw [Real.log_pow (4 : ℝ) n] at h_log
  exact h_log

/-!
=============================================================================
PART 2: Chebyshev Prime Energy Sum and Product Dominance
=============================================================================
-/

/-- Chebyshev theta function on a finite set of primes: ∑_{p ∈ P} log p. -/
def chebyshevTheta (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, Real.log (p : ℝ)

/-- Strict positivity of prime log contributions for p ≥ 2. -/
theorem log_prime_pos {p : ℕ} (hp : Nat.Prime p) : 0 < Real.log (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1 : (1 : ℝ) < (p : ℝ) := by linarith
  exact Real.log_pos h1

/-- Positivity of Chebyshev theta sum on nonempty prime finsets. -/
theorem chebyshevTheta_pos (P : Finset ℕ) (hP : P.Nonempty) (h_primes : ∀ p ∈ P, Nat.Prime p) :
    0 < chebyshevTheta P := by
  dsimp [chebyshevTheta]
  apply Finset.sum_pos
  · intro p hp
    exact log_prime_pos (h_primes p hp)
  · exact hP

/-- Logarithmic additivity of prime product: ∑_{p ∈ P} log p = log (∏_{p ∈ P} p). -/
theorem chebyshevTheta_eq_log_prod (P : Finset ℕ) (h_pos : ∀ p ∈ P, 0 < (p : ℝ)) :
    chebyshevTheta P = Real.log (∏ p ∈ P, (p : ℝ)) := by
  dsimp [chebyshevTheta]
  rw [Real.log_prod]
  intro p hp
  exact ne_of_gt (h_pos p hp)

/-- 
  MASTER THEOREM 1 (Chebyshev Prime Interval Energy Bound):
  For any prime subset P whose product is bounded by the central binomial coefficient (2n choose n):
    θ(P) ≤ n * log 4.
-/
theorem chebyshev_interval_energy_bound
    (n : ℕ) (P : Finset ℕ)
    (h_pos : ∀ p ∈ P, 0 < (p : ℝ))
    (h_prod_le : (∏ p ∈ P, (p : ℝ)) ≤ (Nat.choose (2 * n) n : ℝ)) :
    chebyshevTheta P ≤ (n : ℝ) * Real.log 4 := by
  have h_prod_pos : 0 < (∏ p ∈ P, (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    exact h_pos p hp
  have h_log_prod := chebyshevTheta_eq_log_prod P h_pos
  have h_log_le : Real.log (∏ p ∈ P, (p : ℝ)) ≤ Real.log (Nat.choose (2 * n) n : ℝ) :=
    Real.log_le_log h_prod_pos h_prod_le
  have h_binom_le := log_choose_two_mul_le_mul_log_four n
  rw [← h_log_prod] at h_log_le
  linarith

/-- The divisibility form used for prime divisors of the central binomial
coefficient.  The arithmetic hypothesis is kept explicit: the logarithmic
bound itself only needs the resulting product inequality. -/
theorem chebyshev_theta_le_of_prod_dvd
    (n : ℕ) (P : Finset ℕ)
    (h_pos : ∀ p ∈ P, 0 < (p : ℝ))
    (h_dvd : (∏ p ∈ P, p) ∣ Nat.choose (2 * n) n) :
    chebyshevTheta P ≤ (n : ℝ) * Real.log 4 := by
  have h_prod_nat_pos : 0 < ∏ p ∈ P, p := by
    apply Finset.prod_pos
    intro p hp
    have hp' : 0 < p := by
      exact_mod_cast h_pos p hp
    exact hp'
  have h_choose_pos : 0 < Nat.choose (2 * n) n := by
    apply Nat.choose_pos
    have : n ≤ 2 * n := by omega
    exact this
  have h_prod_nat_le : (∏ p ∈ P, p) ≤ Nat.choose (2 * n) n :=
    Nat.le_of_dvd h_choose_pos h_dvd
  have h_prod_le : (∏ p ∈ P, (p : ℝ)) ≤ (Nat.choose (2 * n) n : ℝ) := by
    have h_cast_prod : ((∏ p ∈ P, p : ℕ) : ℝ) = ∏ p ∈ P, (p : ℝ) := by
      simp
    rw [← h_cast_prod]
    exact_mod_cast h_prod_nat_le
  exact chebyshev_interval_energy_bound n P h_pos h_prod_le

/-- 
  MASTER THEOREM 2: Chebyshev Prime Energy Dominance Bound.
  For any prime subset P whose product is bounded by M:
    θ(P) ≤ log M.
-/
theorem chebyshev_theta_le_of_prod_le
    (P : Finset ℕ) (M : ℝ)
    (h_pos : ∀ p ∈ P, 0 < (p : ℝ))
    (h_prod_le : (∏ p ∈ P, (p : ℝ)) ≤ M)
    (h_prod_pos : 0 < (∏ p ∈ P, (p : ℝ))) :
    chebyshevTheta P ≤ Real.log M := by
  rw [chebyshevTheta_eq_log_prod P h_pos]
  exact Real.log_le_log h_prod_pos h_prod_le

end InfoGeometry.Arithmetic.Chebyshev

end noncomputable section
