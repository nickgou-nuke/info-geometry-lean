import Mathlib.Data.Nat.Fib.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace Omega.Generated

/-- GCD identity: gcd(F(m), F(n)) = F(gcd(m,n)). Source: Omega.Core.Fib -/
theorem fib_gcd (m n : Nat) : Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n) :=
  (Nat.fib_gcd m n).symm

end Omega.Generated
