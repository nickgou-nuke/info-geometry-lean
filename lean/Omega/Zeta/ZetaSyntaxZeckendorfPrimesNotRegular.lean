import Omega.Zeta.ZetaSyntaxZeckendorfPrimesNotSofic

namespace Omega.Zeta

/-- Successor-form corollary of the Fibonacci index bound. This does not
assert that a language is non-regular. -/
theorem zeta_syntax_zeckendorf_fibonacci_successor_bound
    (m : ℕ) : m + 1 ≤ Nat.fib (m + 2) := by
  exact Nat.succ_le_of_lt (zeta_syntax_zeckendorf_fibonacci_bound m)

end Omega.Zeta
