import Mathlib
import InfoGeometry.Arithmetic.BostConnesSystem

/-!
# Prime Factor Count — Ω(p^k) = k

Two theorems connecting the arithmetic of prime factorization to
the Liouville function, proved using the existing infrastructure
in BostConnesSystem.lean.

Reference: Bost–Connes (1995), Section 2: The Primon Gas.
-/

open InfoGeometry.Arithmetic.BostConnesSystem

namespace PrimeFactorCount

/--
**Ω(p^k) = k.** For any prime p and any k ≥ 0, the total number of
prime factors of p^k counted with multiplicity is exactly k.

Proof by induction using complete additivity (`totalPrimeFactors_mul`)
and the base case Ω(p) = 1 (`totalPrimeFactors_prime`).
-/
theorem totalPrimeFactors_prime_pow (p : ℕ+) (hp : Nat.Prime p.val) (k : ℕ) :
    totalPrimeFactors (p ^ k) = k := by
  induction' k with k ih
  · simp
  · rw [pow_succ, totalPrimeFactors_mul, ih, totalPrimeFactors_prime p hp]

/--
**λ(p^k) = (-1)^k.** Direct consequence of the Liouville function
definition `λ(n) = (-1)^{Ω(n)}` and the theorem `Ω(p^k) = k`.

For even k, λ(p^k) = 1. For odd k, λ(p^k) = -1.
-/
theorem liouville_prime_pow (p : ℕ+) (hp : Nat.Prime p.val) (k : ℕ) :
    liouville (p ^ k) = (-1 : ℤ) ^ k := by
  rw [liouville, InfoGeometry.Arithmetic.BostConnesSystem.Omega_prime_pow p.val k hp]

end PrimeFactorCount
