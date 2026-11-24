/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Nat.Fib.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace Omega.Generated.FibGcd

/-- GCD identity: gcd(F(m), F(n)) = F(gcd(m,n)). Source: Omega.Core.Fib -/
theorem fib_gcd (m n : Nat) : Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n) :=
  (Nat.fib_gcd m n).symm

end Omega.Generated.FibGcd
