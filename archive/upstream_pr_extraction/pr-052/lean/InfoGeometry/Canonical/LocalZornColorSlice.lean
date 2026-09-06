import Mathlib
import InfoGeometry.Canonical.LocalZornCl11Slice

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra
open scoped LinearAlgebra.Projectivization

/-!
# The three local associative Zorn--Clifford slices

The color index chooses a coordinate direction only.  All multiplication and
projective statements below are inherited from the fixed-direction slice; no
associative law is asserted for the ambient Zorn algebra.
-/

inductive ColorSector
  | red
  | green
  | blue
  deriving DecidableEq

def colorDirection : ColorSector → ZornVec3 ℝ
  | .red => ZornVec3.basis 0
  | .green => ZornVec3.basis 1
  | .blue => ZornVec3.basis 2

theorem colorDirection_norm (m : ColorSector) :
    ZornVec3.dot (colorDirection m) (colorDirection m) = 1 := by
  cases m <;> simp [colorDirection, ZornVec3.dot, ZornVec3.basis]

theorem colorDirection_cross_self (m : ColorSector) :
    ZornVec3.cross (colorDirection m) (colorDirection m) = fun _ => 0 := by
  cases m <;> exact ZornVec3.cross_self _

structure LocalZornSlice (m : ColorSector) where
  a : ℝ
  b : ℝ
  u : ℝ
  v : ℝ

namespace LocalZornSlice

def toZorn {m : ColorSector} (X : LocalZornSlice m) : ZornVectorMatrix ℝ :=
  localZornSlice (colorDirection m) X.a X.b X.u X.v

def toMatrix {m : ColorSector} (X : LocalZornSlice m) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  localZornMatrix X.a X.b X.u X.v

def mul {m : ColorSector}
    (X Y : LocalZornSlice m) : LocalZornSlice m :=
  { a := X.a * Y.a + X.u * Y.v
    b := X.b * Y.b + X.v * Y.u
    u := X.a * Y.u + X.u * Y.b
    v := X.v * Y.a + X.b * Y.v }

theorem toZorn_mul {m : ColorSector}
    (X Y : LocalZornSlice m) :
    (mul X Y).toZorn =
      ZornVectorMatrix.mul X.toZorn Y.toZorn := by
  exact (localZornSlice_mul
    (colorDirection m)
    (colorDirection_norm m)
    (colorDirection_cross_self m)
    X.a X.b X.u X.v Y.a Y.b Y.u Y.v).symm

theorem toMatrix_mul {m : ColorSector}
    (X Y : LocalZornSlice m) :
    (mul X Y).toMatrix = X.toMatrix * Y.toMatrix := by
  exact (localZornMatrix_mul X.a X.b X.u X.v Y.a Y.b Y.u Y.v).symm

theorem norm_eq_det {m : ColorSector} (X : LocalZornSlice m) :
    ZornVectorMatrix.norm X.toZorn = Matrix.det X.toMatrix := by
  exact localZornSlice_norm_eq_det
    (colorDirection m) (colorDirection_norm m) X.a X.b X.u X.v

end LocalZornSlice

abbrev LocalZornNormOne (m : ColorSector) :=
  { X : LocalZornSlice m // ZornVectorMatrix.norm X.toZorn = 1 }

def LocalZornNormOne.toSL2 {m : ColorSector} (X : LocalZornNormOne m) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨X.1.toMatrix, by
    rw [← X.1.norm_eq_det]
    exact X.2⟩

def sl2ToLocalZornNormOne (m : ColorSector)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : LocalZornNormOne m :=
  ⟨{ a := g 0 0
     b := g 1 1
     u := g 0 1
     v := g 1 0 }, by
    rw [LocalZornSlice.norm_eq_det]
    simpa only [LocalZornSlice.toMatrix, localZornMatrix,
      Matrix.det_fin_two] using g.property⟩

noncomputable def localZornNormOneEquivSL2 (m : ColorSector) :
    LocalZornNormOne m ≃ Matrix.SpecialLinearGroup (Fin 2) ℝ where
  toFun := LocalZornNormOne.toSL2
  invFun := sl2ToLocalZornNormOne m
  left_inv X := by
    apply Subtype.ext
    cases X with
    | mk X h =>
      cases X
      rfl
  right_inv g := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem localZornNormOneEquivSL2_apply
    (m : ColorSector) (X : LocalZornNormOne m) :
    (localZornNormOneEquivSL2 m X : Matrix (Fin 2) (Fin 2) ℝ) =
      X.1.toMatrix :=
  rfl

end InfoGeometry.Canonical
