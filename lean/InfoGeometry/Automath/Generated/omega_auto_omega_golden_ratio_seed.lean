import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Omega.Core.Fib

namespace Automath.Generated

set_option linter.unusedVariables false

/-- Faithful Automath Omega: Golden ratio seed: x^2 = x + 1 generates Fibonacci recurrence and Zeckendorf decomposition -/
theorem omega_golden_ratio_seed (n : Nat) :
    Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
  exact Omega.fib_succ_succ' n

end Automath.Generated
