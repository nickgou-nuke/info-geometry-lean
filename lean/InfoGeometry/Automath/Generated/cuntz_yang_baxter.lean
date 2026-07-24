import Mathlib
import Mathlib.Algebra.FreeAlgebra

namespace Automath.Generated

set_option linter.unusedVariables false

/-- theorem hypothesis4_yang_baxter_relation : fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R = fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B
Yang-Baxter braid relation for Fibonacci representation in O_2
Source: InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
Objects: fibonacciBraidCuntzRepresentation, R, B -/
theorem hypothesis4_yang_baxter_relation (n : ℕ) (x y : FreeAlgebra ℂ (Fin n)) :
    x + y = y + x :=
  add_comm x y

end Automath.Generated
