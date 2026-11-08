import Mathlib.Data.Nat.Fib.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Linarith

namespace Omega.Generated

/-- Fibonacci recurrence: F(n+2) = F(n+1) + F(n). Source: Omega.Core.Fib -/
theorem fib_succ_succ (n : Nat) : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
  have := Nat.fib_add_two (n := n); omega

end Omega.Generated
