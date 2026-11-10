import Mathlib.Data.Nat.Fib.Basic
import Omega.Zeta.ZeckendorfPrimesNotSofic

namespace Omega.Zeta

/-- Fibonacci index growth bound retained from the source notes. It does not
express a soficity or regularity property of a language. -/
theorem zeta_syntax_zeckendorf_fibonacci_bound :
    ∀ m : ℕ, m < Nat.fib (m + 2) :=
  paper_prime_languages_zeckendorf_fibonacci_bound

end Omega.Zeta
