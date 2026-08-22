import InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
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
  exact (isotropic_iff_splitQuad_zero (octImToImaginary v)).mpr (by
    simpa using hv)

end InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
