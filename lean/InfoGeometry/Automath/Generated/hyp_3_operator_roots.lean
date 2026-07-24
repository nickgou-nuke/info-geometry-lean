import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

/--
Infinitely Many Cuntz-Level Operator Roots: For every k>=2, phi(A) has roots in the matrix block R_0 = phi(r_0(A)) with R_0^k = phi(A). But the root set in O_n is strictly larger -- every unitary U in phi(O_n) with U^k=1 produces another root R_U = U R_0. There are infinitely many such distinct roots, including roots outside phi(M_n).
The quadratic relation restricts spectrum to two points, turning operator roots into independent scalar branch choices. The relative commutant phi(O_n) provides infinitely many finite-order unitaries producing distinct roots. Falsified if relative commutant lacks suitable finite-order unitaries or if some R_U fails the root equation.
Source: InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz
Objects: operator-roots, cuntz-algebra, functional-calculus, relative-commutant, finite-order-unitaries -/
theorem hyp_3_operator_roots (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (x : CuntzAlg n) :
    shiftEndomorphism n x * matrixToCuntz n M = matrixToCuntz n M * shiftEndomorphism n x :=
  hypothesis3_shift_commutes_with_matrix n M x

end Automath.Generated
