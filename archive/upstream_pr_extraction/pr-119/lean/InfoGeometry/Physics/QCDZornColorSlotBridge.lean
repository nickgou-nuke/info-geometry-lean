import Mathlib
import InfoGeometry.Algebra.Zorn.G2TrifactorSU3

/-!
# Zorn three-vector slot bridge for a QCD-facing structural lane

The existing `G2TrifactorSU3` owner proves exact extraction of the upper-right
and lower-left three-vector slots by the diagonal Zorn projectors and proves
that OP-stabilizing composition maps preserve those extraction operations.

This file only re-exports those statements as a QCD-facing structural packet.
It does **not** identify the stabilizer with the physical color group `SU(3)`,
does not identify the slots with quarks/antiquarks, and does not prove
confinement or hadron formation.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDZornColorSlotBridge

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

variable {R : Type*} [CommRing R]

/-- Exact upper/lower three-vector slot extraction packet. -/
theorem zorn_three_vector_slot_packet (X : ZMat R) :
    colorPart X = ({ a := 0, b := 0, x := X.x, y := 0 } : ZMat R) ∧
      anticolorPart X = ({ a := 0, b := 0, x := 0, y := X.y } : ZMat R) :=
  ⟨colorPart_shape X, anticolorPart_shape X⟩

/-- Any explicitly OP-stabilizing composition map preserves both extracted
three-vector slots. -/
theorem op_stabilizer_preserves_three_vector_slots
    (f : ZMat R → ZMat R)
    (hf : IsOPStabilizingCompositionMap f)
    (X : ZMat R) :
    f (colorPart X) = colorPart (f X) ∧
      f (anticolorPart X) = anticolorPart (f X) :=
  ⟨op_stabilizer_preserves_colorPart f hf X,
    op_stabilizer_preserves_anticolorPart f hf X⟩

/-- Determinant preservation implies preservation of the existing Zorn null
cone.  This remains an algebraic norm-cone statement, not a confinement law. -/
theorem determinant_preserving_map_preserves_null_cone
    (f : ZMat R → ZMat R)
    (hdet : ∀ X, InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (f X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X)
    (X : ZMat R)
    (hX : InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull X) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull (f X) :=
  preserves_null_cone_of_det_preserving f hdet X hX

end InfoGeometry.Physics.QCDZornColorSlotBridge

end noncomputable section
