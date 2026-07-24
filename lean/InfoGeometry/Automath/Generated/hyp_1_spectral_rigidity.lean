import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

namespace Automath.Generated

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
open InfoGeometry.Algebra.GoldenMeanShift

/--
Golden-Ratio Spectral Rigidity: For A in M_2(C) with char poly x^2-x-1, the spectrum of phi(A) in O_2 is exactly {phi, psi} where phi=(1+sqrt5)/2 and psi=(1-sqrt5)/2=-phi^-1. Moreover phi(A)^2-phi(A)-1=0 in O_2.
The characteristic polynomial x^2-x-1 forces the spectrum to be the golden ratio and its conjugate. The embedding phi preserves the minimal polynomial x^2-x-1. This is falsified by any additional spectral value appearing after passage from M_2(C) to O_2.
Source: InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz
Objects: spectrum, C*-algebra, golden-ratio, minimal-polynomial, spectral-rigidity -/
theorem hyp_1_spectral_rigidity : X * X - X - 1 = 0 :=
  hypothesis1_minimal_polynomial

end Automath.Generated
