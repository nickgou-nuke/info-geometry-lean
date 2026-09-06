import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
open Matrix
open InfoGeometry.Algebra.CuntzTensorQuotient
open CuntzFibonacciBraidInclusion
open InfoGeometry.Algebra.GoldenMeanShift

/--
Resolvent identity for the Cuntz lift of the golden transfer matrix A in O_2
Source: InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
Objects: matrixToCuntz, CuntzAlg, X, A -/
theorem cuntz_fibonacci_resolvent (mu : ℂ) (hA : IsUnit (mu • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A)) :
    matrixToCuntz 2 ((mu • 1 - A)⁻¹) * (mu • (1 : CuntzAlg 2) - X) = 1 :=
  hypothesis1_resolvent_identity mu hA

end Automath.Generated
