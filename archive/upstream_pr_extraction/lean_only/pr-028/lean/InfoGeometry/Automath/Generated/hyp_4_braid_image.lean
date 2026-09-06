import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
open InfoGeometry.Algebra.CuntzTensorQuotient
open CuntzFibonacciBraidInclusion
open InfoGeometry.Canonical.YangBaxterProof

/--
Fibonacci Braid Image Generates the First Matrix Block: The Fibonacci braid representation generators U = rho(sigma_1) and V = rho(sigma_2) satisfy the non-abelian Yang-Baxter braid relation U V U = V U V with U V != V U.
Source: InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz
Objects: braid-image, yang-baxter, fibonacci, non-abelian -/
theorem hyp_4_braid_image :
    fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R =
    fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B :=
  hypothesis4_yang_baxter_relation

end Automath.Generated
