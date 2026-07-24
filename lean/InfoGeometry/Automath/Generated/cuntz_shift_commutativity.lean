import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
open InfoGeometry.Algebra.CuntzTensorQuotient
open CuntzFibonacciBraidInclusion
open Matrix

/--
Relative shift endomorphism commutes with embedded matrix blocks in O_n
Source: InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
Objects: shiftEndomorphism, matrixToCuntz, CuntzAlg -/
theorem cuntz_shift_commutativity (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (x : CuntzAlg n) :
    shiftEndomorphism n x * matrixToCuntz n M = matrixToCuntz n M * shiftEndomorphism n x :=
  hypothesis3_shift_commutes_with_matrix n M x

end Automath.Generated
