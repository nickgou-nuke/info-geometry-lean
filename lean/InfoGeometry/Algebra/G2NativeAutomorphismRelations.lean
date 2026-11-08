import InfoGeometry.Algebra.SL3NativeAutomorphismTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.SplitCayleyF2

theorem cyclicNativeAutomorphism_pow_three :
    cyclicNativeAutomorphism ^ 3 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact cyclicNativeAutomorphism_cube x

theorem shearNativeAutomorphism_pow_two :
    shearNativeAutomorphism ^ 2 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact shearNativeAutomorphism_square x

end InfoGeometry.Algebra.SplitCayleyF2
