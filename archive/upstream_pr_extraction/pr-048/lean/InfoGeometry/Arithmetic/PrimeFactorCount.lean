import Mathlib.Tactic
import InfoGeometry.Arithmetic.BostConnesSystem


open InfoGeometry.Arithmetic.BostConnesSystem

namespace InfoGeometry.Arithmetic.PrimeFactorCount

theorem totalPrimeFactors_prime_pow (p : ℕ+) (hp : Nat.Prime p.val) (k : ℕ) :
    totalPrimeFactors (p ^ k) = k := by
  induction' k with k ih
  · simp
  · rw [pow_succ, totalPrimeFactors_mul, ih, totalPrimeFactors_prime p hp]

theorem liouville_prime_pow (p : ℕ+) (hp : Nat.Prime p.val) (k : ℕ) :
    liouville (p ^ k) = (-1 : ℤ) ^ k := by
  rw [liouville, InfoGeometry.Arithmetic.BostConnesSystem.Omega_prime_pow p.val k hp]

end InfoGeometry.Arithmetic.PrimeFactorCount
