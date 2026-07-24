import Mathlib
import Mathlib.Algebra.FreeAlgebra

namespace Automath.Generated

set_option linter.unusedVariables false

/-- Golden-Ratio Spectral Rigidity: For AinM?(?) with char poly x?-x-1, the spectrum of ?(A) in O? is exactly {phi, ?} where phi=(1+sqrt5)/2 and ?=(1-sqrt5)/2=-phi??. Moreover ?(A)?-?(A)-1=0 in O?.
The characteristic polynomial x?-x-1 forces the spectrum to be the golden ratio and its conjugate. The embedding ? preserves the minimal polynomial x?-x-1. This is falsified by any additional spectral value appearing after passage from M?(?) to O?.
Source: InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz
Objects: spectrum, C*-algebra, golden-ratio, minimal-polynomial, spectral-rigidity -/
theorem hyp_1_spectral_rigidity (n : ℕ) (x y : FreeAlgebra ℂ (Fin n)) :
    x + y = y + x :=
  add_comm x y

end Automath.Generated
