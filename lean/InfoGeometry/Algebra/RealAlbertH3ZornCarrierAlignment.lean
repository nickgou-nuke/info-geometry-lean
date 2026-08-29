import InfoGeometry.Algebra.RealSplitAlbert
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.RealSplitOctZornAlignment
import InfoGeometry.Algebra.H3ZornCoordinateReadback

namespace InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment

open InfoGeometry.Algebra
open InfoGeometry.Algebra.RealSplitOctZornAlignment
open InfoGeometry.Algebra.H3ZornCoordinateReadback

/-! The existing real Albert and H3Zorn carriers have the same coordinate
shape.  This file records only the carrier, additive, and scalar alignment;
product compatibility is intentionally a separate theorem boundary. -/

def toH3 (X : RealAlbertMatrix) : H3Zorn ℝ :=
  { α₁ := X.α₁
    α₂ := X.α₂
    α₃ := X.α₃
    a := toZorn X.z₃
    b := toZorn X.z₁
    c := toZorn X.z₂ }

def fromH3 (X : H3Zorn ℝ) : RealAlbertMatrix :=
  { α₁ := X.α₁
    α₂ := X.α₂
    α₃ := X.α₃
    z₁ := equiv.symm X.b
    z₂ := equiv.symm X.c
    z₃ := equiv.symm X.a }

def equiv : RealAlbertMatrix ≃ H3Zorn ℝ where
  toFun := toH3
  invFun := fromH3
  left_inv := by
    intro X
    apply RealAlbertMatrix.ext
    · rfl
    · rfl
    · rfl
    · exact fromZorn_toZorn X.z₁
    · exact fromZorn_toZorn X.z₂
    · exact fromZorn_toZorn X.z₃
  right_inv := by
    intro X
    apply H3Zorn.ext_h3
    · rfl
    · rfl
    · rfl
    · exact toZorn_fromZorn X.a
    · exact toZorn_fromZorn X.b
    · exact toZorn_fromZorn X.c

@[simp] theorem equiv_apply (X : RealAlbertMatrix) : equiv X = toH3 X := rfl

@[simp] theorem equiv_symm_apply (X : H3Zorn ℝ) :
    equiv.symm X = fromH3 X := rfl

@[simp] theorem fromH3_z₁ (X : H3Zorn ℝ) :
    (fromH3 X).z₁ = equiv.symm X.b := rfl

@[simp] theorem fromH3_z₂ (X : H3Zorn ℝ) :
    (fromH3 X).z₂ = equiv.symm X.c := rfl

@[simp] theorem fromH3_z₃ (X : H3Zorn ℝ) :
    (fromH3 X).z₃ = equiv.symm X.a := rfl

theorem toH3_add (X Y : RealAlbertMatrix) :
    toH3 (RealAlbertMatrix.add X Y) = toH3 X + toH3 Y := by
  rw [H3Zorn.add_readback]
  apply H3Zorn.ext_h3
  · rfl
  · rfl
  · rfl
  · exact toZorn_add X.z₃ Y.z₃
  · exact toZorn_add X.z₁ Y.z₁
  · exact toZorn_add X.z₂ Y.z₂

theorem toH3_smul (r : ℝ) (X : RealAlbertMatrix) :
    toH3 (RealAlbertMatrix.smul r X) = r • toH3 X := by
  rw [H3Zorn.smul_readback]
  apply H3Zorn.ext_h3
  · rfl
  · rfl
  · rfl
  · exact toZorn_smul r X.z₃
  · exact toZorn_smul r X.z₁
  · exact toZorn_smul r X.z₂

@[simp] theorem toH3_linearTrace (X : RealAlbertMatrix) :
    H3Zorn.linearTrace (toH3 X) = X.α₁ + X.α₂ + X.α₃ := by
  rfl

theorem toH3_traceBilin (X Y : RealAlbertMatrix) :
    H3Zorn.traceBilin (toH3 X) (toH3 Y) =
      X.α₁ * Y.α₁ + X.α₂ * Y.α₂ + X.α₃ * Y.α₃ +
        ZornVectorMatrix.trace
          (ZornVectorMatrix.mul (toZorn X.z₃)
            (ZornVectorMatrix.conj (toZorn Y.z₃))) +
        ZornVectorMatrix.trace
          (ZornVectorMatrix.mul (toZorn X.z₁)
            (ZornVectorMatrix.conj (toZorn Y.z₁))) +
        ZornVectorMatrix.trace
          (ZornVectorMatrix.mul (toZorn X.z₂)
            (ZornVectorMatrix.conj (toZorn Y.z₂))) := by
  rfl

end InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment
