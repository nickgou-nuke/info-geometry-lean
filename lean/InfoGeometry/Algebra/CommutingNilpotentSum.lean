import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.CommutingNilpotentSum

Owner theorem for tensor-growth of logarithmic nilpotency.

If two elements commute and satisfy `A^m = 0` and `B^n = 0`, then their sum
satisfies

`(A + B)^(m + n - 1) = 0`.

The proof is the commuting noncommutative binomial theorem: every monomial on
the antidiagonal of total degree `m+n-1` contains either at least `m` copies of
`A` or at least `n` copies of `B`.
-/

namespace InfoGeometry.Algebra.CommutingNilpotentSum

open scoped BigOperators

variable {R : Type*} [Semiring R]

/-- A power above a vanishing power also vanishes. -/
theorem pow_eq_zero_of_pow_eq_zero_of_le
    (A : R) {m k : ℕ} (hm : A ^ m = 0) (hmk : m ≤ k) :
    A ^ k = 0 := by
  have hk : m + (k - m) = k := Nat.add_sub_of_le hmk
  calc
    A ^ k = A ^ (m + (k - m)) := by rw [hk]
    _ = A ^ m * A ^ (k - m) := by rw [pow_add]
    _ = 0 := by rw [hm, zero_mul]

/-- Sum of commuting nilpotents: if `A^m = 0` and `B^n = 0`, then
`(A+B)^(m+n-1)=0`. -/
theorem add_pow_eq_zero_of_commute_of_pow_eq_zero
    (A B : R) (m n : ℕ)
    (hcomm : Commute A B)
    (hA : A ^ m = 0)
    (hB : B ^ n = 0) :
    (A + B) ^ (m + n - 1) = 0 := by
  rw [hcomm.add_pow']
  apply Finset.sum_eq_zero
  intro p hp
  have hsum : p.1 + p.2 = m + n - 1 := by
    simpa using hp
  have hlarge : m ≤ p.1 ∨ n ≤ p.2 := by
    omega
  rcases hlarge with hleft | hright
  · have hpA : A ^ p.1 = 0 :=
      pow_eq_zero_of_pow_eq_zero_of_le A hA hleft
    simp [hpA]
  · have hpB : B ^ p.2 = 0 :=
      pow_eq_zero_of_pow_eq_zero_of_le B hB hright
    simp [hpB]

end InfoGeometry.Algebra.CommutingNilpotentSum
