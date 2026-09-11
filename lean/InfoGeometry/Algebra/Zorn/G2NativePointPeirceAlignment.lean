/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Concrete readback from the seven-coordinate imaginary carrier to the
split-octonion Peirce carrier. -/

namespace InfoGeometry.Algebra.Zorn.G2NativePointPeirceAlignment

open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2NativePointFoundation
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem nativeBasePoint_imaginary_value :
    (octImToImaginary nativeBasePoint).1 = up2 := by
  apply SplitOctF2.ext <;>
    native_decide

theorem pcWord_nativeBasePoint_imaginary_value (e : Fin 6 → Bool) :
    (octImToImaginary
      (octImAction
        (G2TwoSylowPCAutomorphisms.pcWord e) nativeBasePoint)).1 = up2 := by
  rw [G2NativeOnePointStabilizer.pcWord_fix]
  exact nativeBasePoint_imaginary_value

end InfoGeometry.Algebra.Zorn.G2NativePointPeirceAlignment
