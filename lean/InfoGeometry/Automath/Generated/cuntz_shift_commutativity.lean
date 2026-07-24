import Mathlib
import Mathlib.Algebra.FreeAlgebra

namespace Automath.Generated

set_option linter.unusedVariables false

/-- theorem hypothesis3_shift_commutes_with_matrix (n : ?) (M : Matrix (Fin n) (Fin n) ?) (x : CuntzAlg n) : shiftEndomorphism n x * matrixToCuntz n M = matrixToCuntz n M * shiftEndomorphism n x
Relative shift endomorphism commutes with embedded matrix blocks in O_n
Source: InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
Objects: shiftEndomorphism, matrixToCuntz, CuntzAlg -/
theorem cuntz_shift_commutativity (n : ℕ) (x y : FreeAlgebra ℂ (Fin n)) :
    x + y = y + x :=
  add_comm x y

end Automath.Generated
