import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

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
open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

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

theorem embed_octImAction (f : SplitOctF2Aut) (v : OctImF2) :
    embed (octImAction f v) = f⁻¹.1 (embed v) := by
  unfold embed octImAction
  change (octImToImaginary (imaginaryToOctIm
    (InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints.actImaginary f
      (octImToImaginary v)))).1 = f⁻¹.1 (octImToImaginary v).1
  exact congrArg (fun z : InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints.Imaginary => z.1)
    (imaginaryOctImEquiv.left_inv
      (InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints.actImaginary f
        (octImToImaginary v)))

theorem nativeIncident_octImAction_iff
    (f : SplitOctF2Aut) (x y : OctImF2)
    (hx : splitQuad x = 0) (hy : splitQuad y = 0) :
    nativeIncident (embed (octImAction f x)) (embed (octImAction f y)) ↔
      nativeIncident (embed x) (embed y) := by
  rw [embed_octImAction, embed_octImAction]
  apply nativeIncident_map_iff (f⁻¹ : SplitOctF2Aut)
  · exact (octImToImaginary x).2
  · exact (octImToImaginary y).2
  · apply (isotropic_iff_splitQuad_zero (octImToImaginary x)).mpr
    have hcoord : imaginaryToOctIm (octImToImaginary x) = x :=
      imaginaryOctImEquiv.right_inv x
    rw [hcoord]
    exact hx
  · apply (isotropic_iff_splitQuad_zero (octImToImaginary y)).mpr
    have hcoord : imaginaryToOctIm (octImToImaginary y) = y :=
      imaginaryOctImEquiv.right_inv y
    rw [hcoord]
    exact hy

end InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
