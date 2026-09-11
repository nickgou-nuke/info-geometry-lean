import InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberActionReadback

/-!
# Concrete readback for the parabolic line representatives

These lemmas specialize the generic native fibre readback to the two chosen
parabolic generators.  The proof remains transport-based: no enumeration of
the line fibre is used.
-/

namespace InfoGeometry.Algebra.Zorn.G2ParabolicLineReadbackBridge

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2NativePointFoundation
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberActionReadback

theorem parabolicReflection_baseLineVector_readback :
    (lineInfinity : NativeLine).1 =
      lineSet (octImAction parabolicReflection baseLineVector) := by
  unfold lineInfinity nativeLineAction lineZero nativeBaseLineWitness
    nativeLineFiberMap
  change (lineSet baseLineVector).image
      (octImAction parabolicReflection) = _
  exact (lineSet_action parabolicReflection
    (by simpa [parabolicReflection] using swap01Aut_fix_nativeBasePoint)
    baseLineVector).symm

theorem lineShear_lineInfinityVector_readback :
    (lineOne : NativeLine).1 =
      lineSet (octImAction lineShear
        (octImAction parabolicReflection baseLineVector)) := by
  unfold lineOne nativeLineAction nativeLineFiberMap
  change lineInfinity.1.image (octImAction lineShear) = _
  rw [parabolicReflection_baseLineVector_readback]
  exact (lineSet_action lineShear (pcGenerator_fix 0)
    (octImAction parabolicReflection baseLineVector)).symm

end InfoGeometry.Algebra.Zorn.G2ParabolicLineReadbackBridge
