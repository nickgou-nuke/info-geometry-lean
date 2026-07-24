import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
open InfoGeometry.Algebra.GoldenMeanShift

/--
Exact Fibonacci Functional Calculus: The embedding phi intertwines holomorphic functional calculus. For all k>=1, phi(A)^k = F_k phi(A) + F_{k-1} 1 = phi(A^k) where F_k are Fibonacci numbers. For all t in R, e^{t phi(A)} = a(t)phi(A) + b(t)1 = phi(e^{tA}) with a(t), b(t) given by Binet-type formulas.
The quadratic relation phi(A)^2 = phi(A) + 1 collapses every analytic function of phi(A) to a linear remainder modulo x^2-x-1, converting the additive parameter t into a Fibonacci-type multiplicative semigroup. Falsified by any k or t where equality fails in O_2 norm.
Source: InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz
Objects: functional-calculus, fibonacci, exponential, holomorphic-functional-calculus, spectrum -/
theorem hyp_2_fibonacci_functional_calculus (k : ℕ) :
    X ^ k = algebraMap ℂ (CuntzAlg 2) (fibA k) + algebraMap ℂ (CuntzAlg 2) (fibB k) * X :=
  hypothesis2_power_calculus k

end Automath.Generated
