import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
import InfoGeometry.Algebra.Zorn.G2NativePointFoundation

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
open InfoGeometry.Algebra.Zorn.G2NativePointFoundation

def embed (v : OctImF2) : SplitOctF2 := (octImToImaginary v).1

def nativeCandidateAt (x y : OctImF2) : Prop :=
  y ≠ 0 ∧ y ≠ x ∧ mul (embed x) (embed y) = zero

instance (x : OctImF2) : DecidablePred (nativeCandidateAt x) := by
  intro y
  unfold nativeCandidateAt
  infer_instance

def nativeLineSetAt (x y : OctImF2) : Finset OctImF2 :=
  {x, y, x + y}

def nativeLinesAt (x : OctImF2) : Finset (Finset OctImF2) :=
  (Finset.univ.filter (nativeCandidateAt x)).image (nativeLineSetAt x)

def NativeLinesThroughPoint (x₀ : OctImF2) : Type :=
  {L : Finset OctImF2 // L ∈ nativeLinesAt x₀}

instance (x₀ : OctImF2) : Fintype (NativeLinesThroughPoint x₀) :=
  Subtype.fintype _

instance (x₀ : OctImF2) : DecidableEq (NativeLinesThroughPoint x₀) := by
  dsimp [NativeLinesThroughPoint]
  infer_instance

abbrev NativeBaseLine := NativeLinesThroughPoint nativeBasePoint

instance : Fintype NativeBaseLine := inferInstance

theorem nativeBaseLine_card : Fintype.card NativeBaseLine =
    Fintype.card (NativeLinesThroughPoint nativeBasePoint) := by
  rfl

def nativeBaseLineSet : Finset OctImF2 :=
  Finset.univ.filter (nativeCandidateAt nativeBasePoint)

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

theorem native_multiplication_zero_iff
    (f : SplitOctF2Aut) (x y : OctImF2) :
    mul (embed (octImAction f x)) (embed (octImAction f y)) = zero ↔
      mul (embed x) (embed y) = zero := by
  rw [embed_octImAction, embed_octImAction]
  constructor
  · intro h
    have h' := congrArg f.1 h
    rw [f.2.2.2] at h'
    have hfzero : f.1 zero = zero := by
      calc
        f.1 zero = f.1 (add zero zero) := by
          rw [add_zero]
        _ = add (f.1 zero) (f.1 zero) := f.2.2.1 zero zero
        _ = zero := add_self (f.1 zero)
    change mul (f.1 (f.1.symm (embed x))) (f.1 (f.1.symm (embed y))) = f.1 zero at h'
    simpa [f.1.apply_symm_apply, hfzero] using h'
  · intro h
    have h' := congrArg f⁻¹.1 h
    rw [f⁻¹.2.2.2] at h'
    have hinvzero : f⁻¹.1 zero = zero := by
      calc
        f⁻¹.1 zero = f⁻¹.1 (add zero zero) := by
          rw [add_zero]
        _ = add (f⁻¹.1 zero) (f⁻¹.1 zero) := f⁻¹.2.2.1 zero zero
        _ = zero := add_self (f⁻¹.1 zero)
    change mul (f⁻¹.1 (embed x)) (f⁻¹.1 (embed y)) = f⁻¹.1 zero at h'
    simpa [hinvzero] using h'

end InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
