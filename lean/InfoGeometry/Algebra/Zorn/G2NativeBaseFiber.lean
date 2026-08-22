import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

/-!
# Native split-Zorn base fiber

The line fiber at the standard isotropic point is defined from the native
split-Zorn multiplication, not from the rejected coordinate operation
`octCross`.  This is the local carrier from which a global flag incidence
relation can be transported.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeBaseFiber

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

def embed (v : OctImF2) : SplitOctF2 := (octImToImaginary v).1

def nativeBaseLine (y : OctImF2) : Prop :=
  splitQuad y = 0 ∧ y ≠ 0 ∧ y 0 = 0 ∧
    mul (embed basePoint) (embed y) = zero

instance : DecidablePred nativeBaseLine := by
  intro y
  unfold nativeBaseLine
  infer_instance

def NativeBaseLine := {y : OctImF2 // nativeBaseLine y}

instance : Fintype NativeBaseLine := Subtype.fintype nativeBaseLine

theorem nativeBaseLine_card : Fintype.card NativeBaseLine = 3 := by
  native_decide

end InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
