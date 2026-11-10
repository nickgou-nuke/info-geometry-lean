import Omega.Zeta.ZeckendorfPrimesNotSofic

namespace Omega.Zeta

/-- Fibonacci index growth bound used by the source notes. It is not a
non-soficity theorem. -/
theorem paper_etds_zeckendorf_fibonacci_bound :
    ∀ m : ℕ, m < Nat.fib (m + 2) :=
  paper_prime_languages_zeckendorf_fibonacci_bound

end Omega.Zeta
