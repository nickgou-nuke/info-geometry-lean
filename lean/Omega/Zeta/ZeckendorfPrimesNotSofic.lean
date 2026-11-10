import Omega.Zeta.DFADensityDichotomy

namespace Omega.Zeta

/-- Fibonacci index growth bound. This arithmetic statement is not a language
non-regularity or non-soficity theorem. -/
theorem paper_prime_languages_zeckendorf_fibonacci_bound :
    ∀ m : ℕ, m < Nat.fib (m + 2) :=
  Omega.Zeta.DFADensityDichotomy.fib_gt_linear

end Omega.Zeta
