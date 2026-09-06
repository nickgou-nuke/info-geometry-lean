import InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2NativeLineFiber

namespace InfoGeometry.Algebra.Zorn.G2NativeLineFiberIdentity

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction

theorem nativeLineAction_one
    (L : G2NativeLineFiber.NativeLine) :
    nativeLineAction 1
      (G2NativeLineFiber.octImAction_one
        G2NativePointFoundation.nativeBasePoint) L = L := by
  unfold nativeLineAction
  apply Subtype.ext
  change L.1.image (octImAction 1) = L.1
  have haction : octImAction 1 = id := by
    funext x
    exact octImAction_one x
  rw [haction]
  simp

end InfoGeometry.Algebra.Zorn.G2NativeLineFiberIdentity
