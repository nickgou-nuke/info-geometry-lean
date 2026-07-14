import InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket

/-!
# InfoGeometry.Canonical.ConformalFiveGradeCommutatorTable

Direct canonical five-grade commutator table.

This file packages the already-owned direct canonical data into a single table:

* the five-grade inversion carrier;
* the source/sink and incoming/outgoing swaps;
* the grade-zero stability;
* the finite matrix-unit Wick readout.

No bridge surface is introduced.
-/

noncomputable section

namespace ConformalFiveGradeCommutatorTable

open InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.ConformalFiveGradeInversion.FiveGradedConformalInversion
open InfoGeometry.Canonical.NormalOrderedCurrent

/--
Direct canonical five-grade commutator table.

The table does not manufacture a new current algebra.  It records the exact
sector swaps and the matrix-unit Wick readout that are already owned by the
imported canonical packets.
-/
structure FiveGradeCommutatorTable
    (L : Type*) (ι : Type*) (R : Type*)
    [Fintype ι] [DecidableEq ι] [Ring R] where
  packet : FiveGradeBoundaryCurrentPacket L ι R

namespace FiveGradeCommutatorTable

variable {L ι R : Type*}
variable [Fintype ι] [DecidableEq ι] [Ring R]

/-- The source-to-sink swap is part of the commutator table. -/
theorem source_to_sink
    (T : FiveGradeCommutatorTable L ι R) (x : L) :
    x ∈ T.packet.sourceSet ↔ T.packet.inversion.theta x ∈ T.packet.sinkSet :=
  T.packet.source_to_sink x

/-- The incoming-to-outgoing swap is part of the commutator table. -/
theorem incoming_to_outgoing
    (T : FiveGradeCommutatorTable L ι R) (x : L) :
    x ∈ T.packet.inversion.incomingSet ↔
      T.packet.inversion.theta x ∈ T.packet.inversion.outgoingSet :=
  T.packet.incoming_to_outgoing x

/-- The modular center is stable under inversion in the commutator table. -/
theorem center_stable
    (T : FiveGradeCommutatorTable L ι R) (x : L) :
    x ∈ T.packet.centerSet ↔ T.packet.inversion.theta x ∈ T.packet.centerSet :=
  T.packet.center_stable x

/-- The matrix-unit Wick readout is the current side of the table. -/
theorem matrixUnitWick_readout
    (T : FiveGradeCommutatorTable L ι R)
    (a b c d : ι) :
    algebraCommutator
        (normalOrderedMatrixUnit (R := R) T.packet.occ a b)
        (normalOrderedMatrixUnit (R := R) T.packet.occ c d)
      =
      (if b = c then normalOrderedMatrixUnit (R := R) T.packet.occ a d else 0)
        - (if a = d then normalOrderedMatrixUnit (R := R) T.packet.occ c b else 0)
        + wickCorrection (R := R) T.packet.occ a b c d :=
  T.packet.matrixUnitWick_readout a b c d

/-- A table obtained directly from a packet. -/
def ofPacket (P : FiveGradeBoundaryCurrentPacket L ι R) :
    FiveGradeCommutatorTable L ι R where
  packet := P

end FiveGradeCommutatorTable

end ConformalFiveGradeCommutatorTable

