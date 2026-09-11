import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.Concrete
import InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
import InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints
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
open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2ImaginaryIsotropicPoints

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

@[simp] theorem boolToZMod_add2 (a b : Bool) :
    boolToZMod (add2 a b) = boolToZMod a + boolToZMod b := by
  cases a <;> cases b <;> rfl

@[simp] theorem boolToZMod_mul2 (a b : Bool) :
    boolToZMod (mul2 a b) = boolToZMod a * boolToZMod b := by
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
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases Y with
    | mk a' b' x0' x1' x2' y0' y1' y2' =>
      dsimp [toZornCell, mul, ZornCell.mulZ]
      congr 1 <;>
        simp [mul2, dot3, cross0, cross1, cross2, boolToZMod_and,
          sub_eq_add_neg] <;> ring

theorem zModToBool_add (a b : ZMod 2) :
    zModToBool (a + b) = (zModToBool a ^^ zModToBool b) := by
  fin_cases a <;> fin_cases b <;> rfl

theorem zModToBool_mul (a b : ZMod 2) :
    zModToBool (a * b) = (zModToBool a && zModToBool b) := by
  fin_cases a <;> fin_cases b <;> rfl

theorem detZ_toZornCell (X : SplitOctF2) :
    ZornCell.detZ (toZornCell X) = boolToZMod (zornNorm X) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  simp [toZornCell, ZornCell.detZ, zornNorm, dot3, mul2, add2,
    boolToZMod_xor, boolToZMod_and, sub_eq_add_neg]
  ring_nf
  cases a <;> cases b <;> cases x0 <;> cases x1 <;> cases x2 <;>
    cases y0 <;> cases y1 <;> cases y2 <;> rfl

def nativePolar (X Y : SplitOctF2) : ZMod 2 :=
  ZornCell.polarZ (toZornCell X) (toZornCell Y)

def nativeIncident (X Y : SplitOctF2) : Prop := nativePolar X Y = 0

theorem boolToZMod_eq_zero_iff (b : Bool) :
    boolToZMod b = 0 ↔ b = false := by
  cases b <;> simp [boolToZMod]

theorem nativePolar_isotropic_sum_iff
    (X Y : SplitOctF2)
    (hX_iso : zornNorm X = false) (hY_iso : zornNorm Y = false) :
    nativeIncident X Y ↔ zornNorm (add X Y) = false := by
  unfold nativeIncident nativePolar
  rw [ZornCell.polarZ]
  rw [← toZornCell_add X Y, detZ_toZornCell, detZ_toZornCell,
    detZ_toZornCell]
  simp [hX_iso, hY_iso, boolToZMod]

theorem traceZero_add {X Y : SplitOctF2}
    (hX : TraceZero X) (hY : TraceZero Y) :
    TraceZero (add X Y) := by
  dsimp [TraceZero] at hX hY ⊢
  simp [add, add2, hX, hY]

theorem nativeIncident_map_iff
    (f : SplitOctF2Aut) (X Y : SplitOctF2)
    (hX_trace : TraceZero X) (hY_trace : TraceZero Y)
    (hX_iso : Isotropic X) (hY_iso : Isotropic Y) :
    nativeIncident (f.1 X) (f.1 Y) ↔ nativeIncident X Y := by
  have hsum_trace : TraceZero (add X Y) := traceZero_add hX_trace hY_trace
  have hsum_iso : Isotropic (add X Y) ↔
      nativeIncident X Y := by
    change zornNorm (add X Y) = false ↔ nativeIncident X Y
    exact (nativePolar_isotropic_sum_iff X Y hX_iso hY_iso).symm
  have hfx_trace : TraceZero (f.1 X) := automorphism_map_traceZero f X hX_trace
  have hfy_trace : TraceZero (f.1 Y) := automorphism_map_traceZero f Y hY_trace
  have hfx_iso : Isotropic (f.1 X) :=
    automorphism_map_isotropic f X hX_trace hX_iso
  have hfy_iso : Isotropic (f.1 Y) :=
    automorphism_map_isotropic f Y hY_trace hY_iso
  have hfsum_trace : TraceZero (f.1 (add X Y)) :=
    automorphism_map_traceZero f (add X Y) hsum_trace
  have hfsum_iso : Isotropic (f.1 (add X Y)) ↔ Isotropic (add X Y) := by
    constructor
    · intro h
      have hi := automorphism_map_isotropic f⁻¹ (f.1 (add X Y))
        hfsum_trace h
      change Isotropic ((f.1).symm (f.1 (add X Y))) at hi
      simpa using hi
    · intro h
      exact automorphism_map_isotropic f (add X Y) hsum_trace h
  have hleft : nativeIncident (f.1 X) (f.1 Y) ↔
      Isotropic (add (f.1 X) (f.1 Y)) := by
    change nativeIncident (f.1 X) (f.1 Y) ↔
      zornNorm (add (f.1 X) (f.1 Y)) = false
    exact nativePolar_isotropic_sum_iff (f.1 X) (f.1 Y) hfx_iso hfy_iso
  rw [hleft, ← f.2.2.1 X Y, hfsum_iso]
  exact hsum_iso

noncomputable def splitOctF2ZornCellEquiv :
    SplitOctF2 ≃ ZornCell (ZMod 2) where
  toFun := toZornCell
  invFun := ofZornCell
  left_inv := ofZornCell_toZornCell
  right_inv := toZornCell_ofZornCell

end InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
