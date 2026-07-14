import InfoGeometry.Arithmetic.BostConnesSystem

/-!
# Finite arithmetic grading packet for the index lane

This file exposes only kernel-checked arithmetic identities already proved in
`BostConnesSystem`. It does not prove a Witten-index/Euler-characteristic
identification, ζ-regularized supersymmetry statement, or anomaly-cancellation
theorem.
-/

namespace IndexTheorem

open InfoGeometry.Arithmetic.BostConnesSystem

/-- The total prime-factor count of `1` is zero. -/
@[simp] theorem totalPrimeFactors_one :
    BostConnesSystem.totalPrimeFactors 1 = 0 :=
  BostConnesSystem.totalPrimeFactors_one

/-- A prime contributes exactly one prime factor. -/
theorem totalPrimeFactors_prime (p : ℕ+) (hp : Nat.Prime p.val) :
    BostConnesSystem.totalPrimeFactors p = 1 :=
  BostConnesSystem.totalPrimeFactors_prime p hp

/-- The Liouville grading is trivial on the vacuum. -/
@[simp] theorem liouville_one :
    BostConnesSystem.liouville 1 = 1 :=
  BostConnesSystem.liouville_one

/-- The Liouville grading always squares to `1`. -/
theorem liouville_sq (n : ℕ+) :
    BostConnesSystem.liouville n * BostConnesSystem.liouville n = 1 :=
  BostConnesSystem.liouville_sq n n.pos

/-- The Liouville grading is multiplicative. -/
theorem liouville_mul (m n : ℕ+) :
    BostConnesSystem.liouville (m * n) =
      BostConnesSystem.liouville m * BostConnesSystem.liouville n :=
  BostConnesSystem.liouville_mul m n m.pos n.pos m.ne_zero n.ne_zero

/-- On a prime, the Liouville grading is `-1`. -/
theorem liouville_prime (p : ℕ+) (hp : Nat.Prime p.val) :
    BostConnesSystem.liouville p = -1 :=
  BostConnesSystem.liouville_prime p hp

/-- Multiplication by a prime flips the Liouville sign. -/
theorem liouville_prime_mul (p n : ℕ+) (hp : Nat.Prime p.val) :
    BostConnesSystem.liouville (p * n) = -BostConnesSystem.liouville n :=
  BostConnesSystem.liouville_prime_mul p n hp n.pos

/--
Open theorem debt for this lane.

The current repository proves the finite arithmetic grading identities above.
Any Witten-index, Euler-characteristic, or anomaly-cancellation statement must
be added later as a theorem with explicit operator/cohomological hypotheses.
-/
def topological_index_debt : String :=
  "Open: state and prove any arithmetic Witten-index/Euler-characteristic bridge with explicit finite/cohomological hypotheses."

end IndexTheorem
