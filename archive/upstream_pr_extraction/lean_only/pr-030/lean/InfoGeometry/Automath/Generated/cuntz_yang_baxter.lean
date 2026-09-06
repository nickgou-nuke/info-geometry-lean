import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
open InfoGeometry.Canonical.YangBaxterProof
open CuntzFibonacciBraidInclusion

/--
Yang-Baxter braid relation for Fibonacci representation in O_2
Source: InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
Objects: fibonacciBraidCuntzRepresentation, R, B -/
theorem hypothesis4_yang_baxter_relation :
    fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R =
    fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B :=
  InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses.hypothesis4_yang_baxter_relation

end Automath.Generated
