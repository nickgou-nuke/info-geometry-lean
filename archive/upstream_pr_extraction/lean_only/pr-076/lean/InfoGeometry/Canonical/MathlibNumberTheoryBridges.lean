import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section

namespace InfoGeometry.Canonical.MathlibNumberTheoryBridges

open scoped BigOperators
open Finset

/-- Prime logarithm is positive. -/
theorem prime_log_pos (p : ℕ) (hp : Nat.Prime p) : 0 < Real.log (p : ℝ) := by
  have h : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast Nat.Prime.one_lt hp
  exact Real.log_pos (by exact_mod_cast h)

/-- The logarithm of a finite product of positive prime factors is additive. -/
theorem sum_log_primes_eq_log_prod (s : Finset ℕ) (hp : ∀ p ∈ s, Nat.Prime p) :
    Finset.sum s (fun p => Real.log (p : ℝ)) =
      Real.log (Finset.prod s (fun p => (p : ℝ))) := by
  rw [Real.log_prod]
  intro p hp'
  exact_mod_cast (Nat.Prime.ne_zero (hp p hp'))

/-- Finite Chebyshev theta readout. -/
noncomputable def chebyshev_theta (x : ℝ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Int.toNat ⌊x⌋))
    (fun p => if Nat.Prime p then Real.log (p : ℝ) else 0)

theorem chebyshev_theta_nonnegative (x : ℝ) : 0 ≤ chebyshev_theta x := by
  unfold chebyshev_theta
  apply Finset.sum_nonneg
  intro p hp
  split_ifs with h
  · exact le_of_lt (prime_log_pos p h)
  · rfl

/-- Finite prime-power logarithmic readout. -/
noncomputable def chebyshev_psi (x : ℝ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Int.toNat ⌊x⌋)) (fun p =>
    Finset.sum (Finset.Icc 1 (Nat.log 2 (Int.toNat ⌊x⌋))) (fun k =>
      if (p : ℕ) ^ k ≤ Int.toNat ⌊x⌋ then Real.log (p : ℝ) else 0))

/-- The prime harmonic finite readout is nonnegative. -/
theorem prime_harmonic_sum_nonnegative (x : ℝ) :
    0 ≤ Finset.sum (Finset.Icc 1 (Int.toNat ⌊x⌋))
      (fun p => if Nat.Prime p then 1 / (p : ℝ) else 0) := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs with h
  · positivity
  · rfl

def primes_mod_4 (a : ℕ) (x : ℝ) : ℕ :=
  (Finset.filter (fun p => p % 4 = a)
    (Finset.filter Nat.Prime (Finset.Icc 1 (Int.toNat ⌊x⌋)))).card

theorem primes_mod_4_nonnegative (a : ℕ) (x : ℝ) :
    0 ≤ (primes_mod_4 a x : ℝ) := by
  exact_mod_cast Nat.zero_le (primes_mod_4 a x)

/-- The finite prime logarithm square sum is nonnegative. -/
theorem prime_log_square_sum_nonnegative (x : ℝ) :
    0 ≤ Finset.sum (Finset.Icc 1 (Int.toNat ⌊x⌋))
      (fun p => if Nat.Prime p then (Real.log (p : ℝ)) ^ 2 else 0) := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact sq_nonneg _
  · rfl

end InfoGeometry.Canonical.MathlibNumberTheoryBridges

end noncomputable section
