import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.Concrete
import Mathlib.Data.ZMod.Basic

/-!
# Coordinate bridge from the native Boolean split-Zorn carrier to `ZornCell`

The two carriers use the same eight coordinates.  This owner records the
actual equivalence and its coordinate round trips; operation transport is
kept separate until its characteristic-two identities are proved.
-/

namespace InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.Concrete

def boolToZMod (b : Bool) : ZMod 2 := if b then 1 else 0

def zModToBool (z : ZMod 2) : Bool := z = 1

theorem boolToZMod_zModToBool (z : ZMod 2) :
    boolToZMod (zModToBool z) = z := by
  fin_cases z <;> rfl

theorem zModToBool_boolToZMod (b : Bool) :
    zModToBool (boolToZMod b) = b := by
  cases b <;> rfl

theorem boolToZMod_xor (a b : Bool) :
    boolToZMod (a ^^ b) = boolToZMod a + boolToZMod b := by
  cases a <;> cases b <;> rfl

theorem boolToZMod_and (a b : Bool) :
    boolToZMod (a && b) = boolToZMod a * boolToZMod b := by
  cases a <;> cases b <;> rfl

def toZornCell (X : SplitOctF2) : ZornCell (ZMod 2) where
  r := boolToZMod X.a
  s := boolToZMod X.b
  x1 := boolToZMod X.x0
  x2 := boolToZMod X.x1
  x3 := boolToZMod X.x2
  y1 := boolToZMod X.y0
  y2 := boolToZMod X.y1
  y3 := boolToZMod X.y2

def ofZornCell (X : ZornCell (ZMod 2)) : SplitOctF2 :=
  ⟨zModToBool X.r, zModToBool X.s,
    zModToBool X.x1, zModToBool X.x2, zModToBool X.x3,
    zModToBool X.y1, zModToBool X.y2, zModToBool X.y3⟩

theorem ofZornCell_toZornCell (X : SplitOctF2) :
    ofZornCell (toZornCell X) = X := by
  cases X
  simp [ofZornCell, toZornCell, zModToBool_boolToZMod]

theorem toZornCell_ofZornCell (X : ZornCell (ZMod 2)) :
    toZornCell (ofZornCell X) = X := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  simp [toZornCell, ofZornCell, boolToZMod_zModToBool]

theorem toZornCell_add (X Y : SplitOctF2) :
    toZornCell (add X Y) = ZornCell.addZ (toZornCell X) (toZornCell Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  simp [toZornCell, add, ZornCell.addZ, add2, boolToZMod_xor]

theorem toZornCell_mul (X Y : SplitOctF2) :
    toZornCell (mul X Y) = ZornCell.mulZ (toZornCell X) (toZornCell Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  simp [toZornCell, mul, ZornCell.mulZ, add2, mul2, dot3, cross0, cross1,
    cross2, boolToZMod_xor, boolToZMod_and, sub_eq_add_neg]
  ring

noncomputable def splitOctF2ZornCellEquiv :
    SplitOctF2 ≃ ZornCell (ZMod 2) where
  toFun := toZornCell
  invFun := ofZornCell
  left_inv := ofZornCell_toZornCell
  right_inv := toZornCell_ofZornCell

end InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
