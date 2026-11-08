import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Omega.CircleDimension

namespace Automath.Generated

set_option linter.unusedVariables false

/-- Faithful Automath Omega: Circle dimension anomaly measures failure of additive hosts for prime-supported frequencies -/
theorem omega_circle_dimension :
    (Omega.CircleDimension.circleDim 0 0 = 0) ∧
      (Omega.CircleDimension.circleDim 0 7 = 0) ∧
      (Omega.CircleDimension.circleDim 0 21 = 0) ∧
      (Omega.CircleDimension.circleDim 1 0 = 1) ∧
      (Omega.CircleDimension.circleDim 2 0 = 2) ∧
      (Omega.CircleDimension.circleDim 3 5 = 3) ∧
      (Omega.CircleDimension.circleDim 1 2 +
        Omega.CircleDimension.circleDim 2 3 =
        Omega.CircleDimension.circleDim 3 5) := by
  exact Omega.CircleDimension.paper_circleDim_basic_certificates

end Automath.Generated
