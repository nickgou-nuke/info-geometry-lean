import InfoGeometry.Algebra.ZeckendorfBijection

namespace Automath.Generated

open InfoGeometry.Algebra.ZeckendorfBijection

set_option linter.unusedVariables false

/-- Faithful Automath Omega: Every positive integer has a unique sum representation in Zeckendorf Fibonacci basis -/
theorem omega_xi_zeta_interface (n : ℕ) :
    ((ourZeckendorf n).map ZeckendorfFib).sum = n :=
  sum_ourZeckendorf n

end Automath.Generated
