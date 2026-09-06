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

def nativeBaseLineSet : Finset OctImF2 :=
  Finset.univ.filter nativeBaseLine

def certifiedBaseLineSet : Finset OctImF2 :=
  Finset.univ.filter (fun y => isG2FlagTransversal basePoint y = true)

theorem nativeBaseLineSet_eq_certifiedBaseLineSet :
    nativeBaseLineSet = certifiedBaseLineSet := by
  native_decide

theorem nativeBaseLine_iff_certified (y : OctImF2) :
    nativeBaseLine y ↔ isG2FlagTransversal basePoint y = true := by
  have h := congrArg (fun s : Finset OctImF2 => y ∈ s)
    nativeBaseLineSet_eq_certifiedBaseLineSet
  simpa [nativeBaseLineSet, certifiedBaseLineSet] using h

noncomputable def nativeBaseLineEquiv :
    NativeBaseLine ≃ LinesThroughPoint basePoint where
  toFun y := ⟨y.1, (nativeBaseLine_iff_certified y.1).mp y.2⟩
  invFun y := ⟨y.1, (nativeBaseLine_iff_certified y.1).mpr y.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

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
