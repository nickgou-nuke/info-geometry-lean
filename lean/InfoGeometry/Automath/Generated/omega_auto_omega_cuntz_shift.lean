import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
open InfoGeometry.Algebra.CuntzTensorQuotient
open CuntzFibonacciBraidInclusion
open Matrix

set_option linter.unusedVariables false

/-- Faithful Automath Omega: Cuntz shift endomorphism on O_n commutes with embedded matrix blocks -/
theorem omega_cuntz_shift (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (x : CuntzAlg n) :
    shiftEndomorphism n x * matrixToCuntz n M = matrixToCuntz n M * shiftEndomorphism n x :=
  hypothesis3_shift_commutes_with_matrix n M x

end Automath.Generated
