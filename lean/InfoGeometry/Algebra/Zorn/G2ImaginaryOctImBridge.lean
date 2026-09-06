import InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
import InfoGeometry.Algebra.Zorn.G2ImaginaryPointAction
import InfoGeometry.Algebra.Zorn.G2PeirceParabolicStabilizer

/-!
# Coordinate bridge from the Boolean Zorn imaginary carrier to `OctImF2`

The native automorphism carrier uses Boolean coordinates, while the finite
Peirce/parabolic geometry uses `ZMod 2` coordinates.  This file freezes their
common seven-coordinate order and proves the quadratic-form compatibility.
-/

namespace InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber

def boolToZMod (b : Bool) : ZMod 2 := if b then 1 else 0

def zModToBool (z : ZMod 2) : Bool := z = 1

theorem boolToZMod_zModToBool (z : ZMod 2) :
    boolToZMod (zModToBool z) = z := by
  fin_cases z <;> rfl

theorem zModToBool_boolToZMod (b : Bool) :
    zModToBool (boolToZMod b) = b := by
  cases b <;> rfl

def imaginaryToOctIm (X : Imaginary) : OctImF2 := fun i =>
  match i with
  | 0 => boolToZMod X.1.x0
  | 1 => boolToZMod X.1.x1
  | 2 => boolToZMod X.1.x2
  | 3 => boolToZMod X.1.y0
  | 4 => boolToZMod X.1.y1
  | 5 => boolToZMod X.1.y2
  | 6 => boolToZMod X.1.a

def octImToImaginary (v : OctImF2) : Imaginary :=
  ⟨⟨zModToBool (v 6), zModToBool (v 6), zModToBool (v 0),
      zModToBool (v 1), zModToBool (v 2), zModToBool (v 3),
      zModToBool (v 4), zModToBool (v 5)⟩, rfl⟩

theorem zModToBool_add (a b : ZMod 2) :
    zModToBool (a + b) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2
        (zModToBool a) (zModToBool b) := by
  fin_cases a <;> fin_cases b <;> rfl

theorem boolToZMod_add2 (a b : Bool) :
    boolToZMod
        (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add2 a b) =
      boolToZMod a + boolToZMod b := by
  cases a <;> cases b <;> rfl

theorem boolToZMod_xor (a b : Bool) :
    boolToZMod (a ^^ b) = boolToZMod a + boolToZMod b := by
  cases a <;> cases b <;> rfl

def imaginaryAdd (A B : Imaginary) : Imaginary :=
  ⟨InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add A.1 B.1, by
    dsimp [InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      TraceZero] at A B ⊢
    rw [A.2, B.2]⟩

theorem imaginaryToOctIm_imaginaryAdd (A B : Imaginary) :
    imaginaryToOctIm (imaginaryAdd A B) =
      imaginaryToOctIm A + imaginaryToOctIm B := by
  funext i
  fin_cases i
  · simp only [imaginaryToOctIm, imaginaryAdd,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [imaginaryToOctIm] using boolToZMod_xor _ _
  · simp only [imaginaryToOctIm, imaginaryAdd,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [imaginaryToOctIm] using boolToZMod_xor _ _
  · simp only [imaginaryToOctIm, imaginaryAdd,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [imaginaryToOctIm] using boolToZMod_xor _ _
  · simp only [imaginaryToOctIm, imaginaryAdd,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [imaginaryToOctIm] using boolToZMod_xor _ _
  · simp only [imaginaryToOctIm, imaginaryAdd,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [imaginaryToOctIm] using boolToZMod_xor _ _
  · simp only [imaginaryToOctIm, imaginaryAdd,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [imaginaryToOctIm] using boolToZMod_xor _ _
  · simp only [imaginaryToOctIm, imaginaryAdd,
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [imaginaryToOctIm] using boolToZMod_xor _ _

theorem actImaginary_imaginaryAdd (f : SplitOctF2Aut) (A B : Imaginary) :
    G2ImaginaryIsotropicPoints.actImaginary f (imaginaryAdd A B) =
      imaginaryAdd (G2ImaginaryIsotropicPoints.actImaginary f A)
        (G2ImaginaryIsotropicPoints.actImaginary f B) := by
  apply Subtype.ext
  change f⁻¹.1 (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add A.1 B.1) =
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
      (f⁻¹.1 A.1) (f⁻¹.1 B.1)
  exact f⁻¹.2.2.1 A.1 B.1

theorem automorphism_map_zero (f : SplitOctF2Aut) : f.1 zero = zero := by
  calc
    f.1 zero = f.1 (add zero zero) := by rw [add_zero]
    _ = add (f.1 zero) (f.1 zero) := f.2.2.1 zero zero
    _ = zero := add_self (f.1 zero)

def imaginaryOctImEquiv : Imaginary ≃ OctImF2 where
  toFun := imaginaryToOctIm
  invFun := octImToImaginary
  left_inv X := by
    rcases X with ⟨⟨a, b, x0, x1, x2, y0, y1, y2⟩, h⟩
    dsimp [TraceZero] at h
    subst b
    apply Subtype.ext
    ext <;> simp [imaginaryToOctIm, octImToImaginary,
      zModToBool, boolToZMod]
  right_inv v := by
    funext i
    fin_cases i <;> simp [imaginaryToOctIm, octImToImaginary,
      boolToZMod_zModToBool]

theorem splitQuad_imaginary (X : Imaginary) :
    splitQuad (imaginaryToOctIm X) =
      boolToZMod (zornNorm X.1) := by
  dsimp [imaginaryToOctIm, splitQuad, zornNorm, boolToZMod]
  native_decide +revert

theorem isotropic_iff_splitQuad_zero (X : Imaginary) :
    Isotropic X.1 ↔ splitQuad (imaginaryToOctIm X) = 0 := by
  rw [splitQuad_imaginary]
  dsimp [Isotropic, zornNorm, boolToZMod]
  native_decide +revert

/-! The native automorphism action can now be transported to the seven
coordinates used by the finite Peirce geometry. -/

def octImAction (g : SplitOctF2Aut) (v : OctImF2) : OctImF2 :=
  imaginaryToOctIm (g • octImToImaginary v)

theorem octImAction_isotropic (g : SplitOctF2Aut) (v : OctImF2)
    (hv : splitQuad v = 0) :
    splitQuad (octImAction g v) = 0 := by
  unfold octImAction
  apply (isotropic_iff_splitQuad_zero (g • octImToImaginary v)).mp
  change Isotropic ((g⁻¹ : SplitOctF2Aut).1 (octImToImaginary v).1)
  apply automorphism_map_isotropic (g⁻¹ : SplitOctF2Aut) (octImToImaginary v).1
    (octImToImaginary v).2
  exact (isotropic_iff_splitQuad_zero (octImToImaginary v)).mpr (by
    have hcoord : imaginaryToOctIm (octImToImaginary v) = v :=
      imaginaryOctImEquiv.right_inv v
    rw [hcoord]
    exact hv)

abbrev OctImIsotropicPoint := {v : OctImF2 // splitQuad v = 0 ∧ v ≠ 0}

open InfoGeometry.Algebra.Zorn.G2ImaginaryPointAction

def pointToOctIm (p : Point) : OctImIsotropicPoint :=
  ⟨imaginaryToOctIm p.1,
    ⟨(isotropic_iff_splitQuad_zero p.1).mp p.2.1, by
      intro h
      apply p.2.2
      apply imaginaryOctImEquiv.injective
      calc
        imaginaryToOctIm p.1 = 0 := h
        _ = imaginaryToOctIm zeroImaginary := by
          symm
          funext i
          fin_cases i <;> rfl
      ⟩⟩

def octImToPoint (v : OctImIsotropicPoint) : Point :=
  ⟨octImToImaginary v.1,
    (isotropic_iff_splitQuad_zero (octImToImaginary v.1)).mpr (by
      have hcoord : imaginaryToOctIm (octImToImaginary v.1) = v.1 :=
        imaginaryOctImEquiv.right_inv v.1
      rw [hcoord]
      exact v.2.1), by
    intro h
    apply v.2.2
    have hz := congrArg imaginaryToOctIm h
    calc
      v.1 = imaginaryToOctIm (octImToImaginary v.1) :=
        (imaginaryOctImEquiv.right_inv v.1).symm
      _ = imaginaryToOctIm zeroImaginary := hz
      _ = 0 := by
        funext i
        fin_cases i <;> rfl⟩

theorem pointToOctIm_left_inverse (p : Point) :
    octImToPoint (pointToOctIm p) = p := by
  apply Subtype.ext
  exact imaginaryOctImEquiv.left_inv p.1

theorem pointToOctIm_right_inverse (v : OctImIsotropicPoint) :
    pointToOctIm (octImToPoint v) = v := by
  apply Subtype.ext
  exact imaginaryOctImEquiv.right_inv v.1

noncomputable def pointOctImEquiv : Point ≃ OctImIsotropicPoint where
  toFun := pointToOctIm
  invFun := octImToPoint
  left_inv := pointToOctIm_left_inverse
  right_inv := pointToOctIm_right_inverse

theorem octImIsotropicPoint_card : Fintype.card OctImIsotropicPoint = 63 := by
  exact (Fintype.card_congr pointOctImEquiv).symm.trans point_card

/-! Transport the native point action across the coordinate equivalence. -/

noncomputable def octImPointPerm (g : SplitOctF2Aut) :
    Equiv.Perm OctImIsotropicPoint :=
  pointOctImEquiv.symm.trans ((MulAction.toPerm g).trans pointOctImEquiv)

theorem octImPointPerm_one : octImPointPerm (1 : SplitOctF2Aut) = 1 := by
  apply Equiv.ext
  intro v
  change pointToOctIm ((1 : SplitOctF2Aut) • octImToPoint v) = v
  rw [one_smul, pointToOctIm_right_inverse]

theorem octImPointPerm_apply (g : SplitOctF2Aut) (v : OctImIsotropicPoint) :
    octImPointPerm g v = pointToOctIm (g • octImToPoint v) := by
  rfl

theorem octImPointPerm_mul (g h : SplitOctF2Aut) :
    octImPointPerm (g * h) = octImPointPerm g * octImPointPerm h := by
  apply Equiv.ext
  intro v
  change pointToOctIm ((g * h) • octImToPoint v) =
    pointToOctIm (g • octImToPoint (pointToOctIm (h • octImToPoint v)))
  rw [mul_smul, pointToOctIm_left_inverse]

end InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
