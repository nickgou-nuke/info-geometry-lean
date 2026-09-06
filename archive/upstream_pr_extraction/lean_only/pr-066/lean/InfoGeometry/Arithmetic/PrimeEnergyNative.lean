import Mathlib

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeEnergyNative

theorem prime_nat_ge_two (p : Nat.Primes) :
    2 ≤ (p : ℕ) :=
  p.2.two_le

theorem prime_nat_gt_one (p : Nat.Primes) :
    1 < (p : ℕ) := by
  exact lt_of_lt_of_le (by decide) (prime_nat_ge_two p)

theorem prime_log_nonneg (p : Nat.Primes) :
    0 ≤ Real.log (p : ℝ) := by
  apply Real.log_nonneg
  have hp : (1 : ℕ) ≤ (p : ℕ) :=
    le_trans (by decide) (prime_nat_ge_two p)
  exact_mod_cast hp

theorem prime_log_pos (p : Nat.Primes) :
    0 < Real.log (p : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (prime_nat_gt_one p)

theorem prime_log_ne_zero (p : Nat.Primes) :
    Real.log (p : ℝ) ≠ 0 :=
  (prime_log_pos p).ne'

end InfoGeometry.Arithmetic.PrimeEnergyNative
