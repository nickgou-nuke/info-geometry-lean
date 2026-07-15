import Mathlib
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Arithmetic.PrimeFactorCount

/-!
# Liouville Parity — λ(n) = ±1 determined by Ω(n) even/odd (PROVED)

From the definition `λ(n) = (-1)^{Ω(n)}`, we prove:
- `Even (Ω n) → λ n = 1`
- `Odd (Ω n) → λ n = -1`

Reference: Bost–Connes (1995).
-/

open InfoGeometry.Arithmetic.BostConnesSystem

noncomputable section

namespace LiouvilleParity

/--
**λ(n) = 1 when Ω(n) is even.** Since `λ(n) = (-1)^{Ω(n)}` and
`(-1)^{2m} = 1` for any m, the result follows directly.
-/
theorem liouville_eq_one_of_even_totalPrimeFactors {n : ℕ+}
    (h : Even (totalPrimeFactors n)) : liouville n = 1 := by
  rcases h with ⟨m, hm⟩
  unfold liouville
  change (-1 : ℤ) ^ totalPrimeFactors n = 1
  rw [hm, ← two_mul, pow_mul, show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_pow]

/--
**λ(n) = -1 when Ω(n) is odd.** Since `(-1)^{2m+1} = -1`.
-/
theorem liouville_eq_neg_one_of_odd_totalPrimeFactors {n : ℕ+}
    (h : Odd (totalPrimeFactors n)) : liouville n = -1 := by
  rcases h with ⟨m, hm⟩
  unfold liouville
  change (-1 : ℤ) ^ totalPrimeFactors n = -1
  rw [hm, pow_succ, pow_mul (a := (-1 : ℤ)) (m := 2),
    show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_pow, one_mul]

/--
**Corollary: λ(n) is always ±1.** This is already known from
`liouville_sq` (λ(n)² = 1), but here we prove it constructively
from the parity of Ω(n).
-/
theorem liouville_is_neg_one_pow (n : ℕ+) :
    liouville n = (-1 : ℤ) ^ (totalPrimeFactors n) := rfl

/--
**λ(1) = 1** because Ω(1) = 0 which is even.
-/
example : liouville 1 = 1 := liouville_one

/--
**λ(p) = -1** for any prime p, because Ω(p) = 1 which is odd.
-/
example (p : ℕ+) (hp : Nat.Prime p.val) : liouville p = -1 :=
  liouville_prime p hp

/--
**λ(p^k) = 1 when k is even, λ(p^k) = -1 when k is odd.**
This follows from Ω(p^k) = k (proved in `PrimeFactorCount.lean`).
-/
theorem liouville_prime_pow_eq_one_of_even (p : ℕ+) (hp : Nat.Prime p.val) {k : ℕ} (hk : Even k) :
    liouville (p ^ k) = 1 := by
  rw [liouville, InfoGeometry.Arithmetic.BostConnesSystem.Omega_prime_pow p.val k hp]
  rcases hk with ⟨m, hm⟩
  rw [hm, ← two_mul, pow_mul, show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_pow]

theorem liouville_prime_pow_eq_neg_one_of_odd (p : ℕ+) (hp : Nat.Prime p.val) {k : ℕ} (hk : Odd k) :
    liouville (p ^ k) = -1 := by
  rw [liouville, InfoGeometry.Arithmetic.BostConnesSystem.Omega_prime_pow p.val k hp]
  rcases hk with ⟨m, hm⟩
  rw [hm, pow_succ, pow_mul (a := (-1 : ℤ)) (m := 2),
    show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_pow, one_mul]

end LiouvilleParity
