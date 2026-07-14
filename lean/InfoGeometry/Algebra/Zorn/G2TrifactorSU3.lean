import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Algebra.Zorn.Composition

/-!
# Zorn Trifactor Projectors and Color Slots

This module owns the finite algebraic part of the proposed
Zorn/trifactor/SU(3) bridge.

#### BUCKET 1: CLOSED FINITE THEOREMS
The canonical Zorn vector-matrix product preserves the diagonal projectors
`OP1` and `OP2` as idempotent and cubic projectors. Sandwiching a Zorn cell by
`OP1` and `OP2` extracts exactly the upper-right three-vector slot, while the
opposite sandwich extracts the lower-left three-vector slot.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
An `OP`-stabilizing multiplication-preserving map commutes with these
extraction operations. A map preserves the Zorn null cone when an explicit
determinant-preservation premise is supplied.

#### BUCKET 3: OPEN CLOSURE DEBT
No full theorem in this file identifies the stabilizer with the Lie group
`SU(3)`, constructs the split-octonion automorphism group `G₂`, or proves a
physical strong-force interpretation. Those require separate Lie-group and
representation-theoretic owners.
-/

noncomputable section

namespace G2TrifactorSU3

open InfoGeometry.Algebra.Zorn

abbrev ZMat (R : Type*) [CommRing R] := InfoGeometry.Canonical.ZornMatrix R

variable {R : Type*} [CommRing R]

/-- The canonical Zorn product used by the finite projector owner. -/
def zMul (X Y : ZMat R) : ZMat R where
  a := X.a * Y.a + InfoGeometry.Canonical.ZornMatrix.dot X.x Y.y
  b := X.b * Y.b + InfoGeometry.Canonical.ZornMatrix.dot X.y Y.x
  x := X.a • Y.x + Y.b • X.x - InfoGeometry.Canonical.ZornMatrix.cross X.y Y.y
  y := X.b • Y.y + Y.a • X.y + InfoGeometry.Canonical.ZornMatrix.cross X.x Y.x

/-- The upper diagonal projector `[1, 0; 0, 0]`. -/
def OP1 : ZMat R :=
  { a := 1, b := 0, x := 0, y := 0 }

/-- The lower diagonal projector `[0, 0; 0, 1]`. -/
def OP2 : ZMat R :=
  { a := 0, b := 1, x := 0, y := 0 }

/-- `OP1` is an idempotent for the canonical Zorn product. -/
theorem op1_idempotent :
    zMul (OP1 : ZMat R) OP1 = OP1 := by
  ext i <;>
    simp [OP1, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

/-- `OP2` is an idempotent for the canonical Zorn product. -/
theorem op2_idempotent :
    zMul (OP2 : ZMat R) OP2 = OP2 := by
  ext i <;>
    simp [OP2, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

/-- `OP1` satisfies the cubic/tripotent identity `P^3 = P`. -/
theorem op1_cubic :
    zMul (zMul (OP1 : ZMat R) OP1) OP1 = OP1 := by
  rw [op1_idempotent, op1_idempotent]

/-- `OP2` satisfies the cubic/tripotent identity `P^3 = P`. -/
theorem op2_cubic :
    zMul (zMul (OP2 : ZMat R) OP2) OP2 = OP2 := by
  rw [op2_idempotent, op2_idempotent]

/-- The upper-right three-vector slot isolated as a Zorn cell. -/
def colorPart (X : ZMat R) : ZMat R :=
  zMul (zMul (OP1 : ZMat R) X) OP2

/-- The lower-left three-vector slot isolated as a Zorn cell. -/
def anticolorPart (X : ZMat R) : ZMat R :=
  zMul (zMul (OP2 : ZMat R) X) OP1

/-- Sandwiching by `OP1` and `OP2` extracts exactly the upper-right vector. -/
theorem colorPart_shape (X : ZMat R) :
    colorPart X = ({ a := 0, b := 0, x := X.x, y := 0 } : ZMat R) := by
  ext i <;>
    simp [colorPart, OP1, OP2, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

/-- Sandwiching by `OP2` and `OP1` extracts exactly the lower-left vector. -/
theorem anticolorPart_shape (X : ZMat R) :
    anticolorPart X = ({ a := 0, b := 0, x := 0, y := X.y } : ZMat R) := by
  ext i <;>
    simp [anticolorPart, OP1, OP2, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

/--
A finite algebraic stand-in for an `OP`-stabilizing composition map.

This is deliberately not named as an `SU(3)` theorem: identifying this
stabilizer with an actual Lie group requires a separate group/action owner.
-/
def IsOPStabilizingCompositionMap (f : ZMat R → ZMat R) : Prop :=
  (∀ X Y, f (zMul X Y) = zMul (f X) (f Y)) ∧
    f OP1 = OP1 ∧
    f OP2 = OP2

/-- An `OP`-stabilizing composition map commutes with color-slot extraction. -/
theorem op_stabilizer_preserves_colorPart
    (f : ZMat R → ZMat R)
    (hf : IsOPStabilizingCompositionMap f)
    (X : ZMat R) :
    f (colorPart X) = colorPart (f X) := by
  dsimp [colorPart]
  rcases hf with ⟨h_mul, h_op1, h_op2⟩
  rw [h_mul, h_mul, h_op1, h_op2]

/-- An `OP`-stabilizing composition map commutes with anticolor-slot extraction. -/
theorem op_stabilizer_preserves_anticolorPart
    (f : ZMat R → ZMat R)
    (hf : IsOPStabilizingCompositionMap f)
    (X : ZMat R) :
    f (anticolorPart X) = anticolorPart (f X) := by
  dsimp [anticolorPart]
  rcases hf with ⟨h_mul, h_op1, h_op2⟩
  rw [h_mul, h_mul, h_op1, h_op2]

/--
Null-cone preservation from an explicit determinant-preservation premise.

The determinant premise is the honest finite substitute for the unproved
statement that a given map is a norm-preserving split-octonion automorphism.
-/
theorem preserves_null_cone_of_det_preserving
    (cp : ZornCompositionDatum R)
    (f : ZMat R → ZMat R)
    (hdet : ∀ X, ZornMatrix.detZ cp.toCrossProduct3 (f X) =
      ZornMatrix.detZ cp.toCrossProduct3 X)
    (X : ZMat R)
    (h_null : ZornMatrix.IsNull cp.toCrossProduct3 X) :
    ZornMatrix.IsNull cp.toCrossProduct3 (f X) := by
  unfold ZornMatrix.IsNull at *
  rw [hdet X, h_null]

end G2TrifactorSU3

