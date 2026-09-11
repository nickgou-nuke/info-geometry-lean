import Mathlib.Data.Nat.Fib.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Linarith
import Omega.Core.Fib

namespace Omega.Generated

open Omega

/-- Strict monotonicity: F(m+2) < F(m+3). Source: Omega.Core.Fib -/
theorem fib_lt_fib_succ (m : Nat) : Nat.fib (m + 2) < Nat.fib (m + 3) := by
  have h := fib_succ_succ' (m + 1)
  rw [show m + 1 + 2 = m + 3 from by omega, show m + 1 + 1 = m + 2 from by omega] at h
  have := fib_succ_pos m; omega

/-- Upper bound: F(m+2) ≤ 2^(m+1). Source: Omega.Core.Fib -/
theorem fib_le_pow_two : ∀ m : Nat, Nat.fib (m + 2) ≤ 2 ^ (m + 1)
  | 0 => by simp
  | 1 => by native_decide
  | m + 2 => by
    calc Nat.fib (m + 2 + 2)
        = Nat.fib (m + 2 + 1) + Nat.fib (m + 2) := fib_succ_succ' (m + 2)
      _ ≤ 2 ^ (m + 1 + 1) + 2 ^ (m + 1) :=
          Nat.add_le_add (fib_le_pow_two (m + 1)) (fib_le_pow_two m)
      _ ≤ 2 ^ (m + 1 + 1) + 2 ^ (m + 1 + 1) :=
          Nat.add_le_add_left (Nat.pow_le_pow_right (by omega) (by omega)) _
      _ = 2 ^ (m + 2 + 1) := by ring

/-- GCD identity: gcd(F(m), F(n)) = F(gcd(m,n)). Source: Omega.Core.Fib -/
theorem fib_gcd (m n : Nat) : Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n) :=
  (Nat.fib_gcd m n).symm

end Omega.Generated
