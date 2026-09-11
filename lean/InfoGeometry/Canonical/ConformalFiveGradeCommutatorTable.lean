import InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

namespace InfoGeometry.Canonical.ConformalFiveGradeCommutatorTable

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
abbrev FiveGradeCommutatorTable
    (L : Type*) (ι : Type*) (R : Type*)
    [Fintype ι] [DecidableEq ι] [Ring R] :=
  FiveGradeBoundaryCurrentPacket L ι R

namespace FiveGradeCommutatorTable

variable {L ι R : Type*}
variable [Fintype ι] [DecidableEq ι] [Ring R]

/-- Compatibility readout; the table is the canonical boundary packet itself. -/
abbrev packet (T : FiveGradeCommutatorTable L ι R) :
    FiveGradeBoundaryCurrentPacket L ι R :=
  T

/-- The source-to-sink swap is part of the commutator table. -/
theorem source_to_sink
    (T : FiveGradeCommutatorTable L ι R) (x : L) :
    x ∈ T.sourceSet ↔ T.inversion.theta x ∈ T.sinkSet :=
  FiveGradeBoundaryCurrentPacket.source_to_sink T x

/-- The incoming-to-outgoing swap is part of the commutator table. -/
theorem incoming_to_outgoing
    (T : FiveGradeCommutatorTable L ι R) (x : L) :
    x ∈ T.inversion.incomingSet ↔
      T.inversion.theta x ∈ T.inversion.outgoingSet :=
  FiveGradeBoundaryCurrentPacket.incoming_to_outgoing T x

/-- The modular center is stable under inversion in the commutator table. -/
theorem center_stable
    (T : FiveGradeCommutatorTable L ι R) (x : L) :
    x ∈ T.centerSet ↔ T.inversion.theta x ∈ T.centerSet :=
  FiveGradeBoundaryCurrentPacket.center_stable T x

/-- The matrix-unit Wick readout is the current side of the table. -/
theorem matrixUnitWick_readout
    (T : FiveGradeCommutatorTable L ι R)
    (a b c d : ι) :
    algebraCommutator
        (normalOrderedMatrixUnit (R := R) T.occ a b)
        (normalOrderedMatrixUnit (R := R) T.occ c d)
      =
      (if b = c then normalOrderedMatrixUnit (R := R) T.occ a d else 0)
        - (if a = d then normalOrderedMatrixUnit (R := R) T.occ c b else 0)
        + wickCorrection (R := R) T.occ a b c d :=
  FiveGradeBoundaryCurrentPacket.matrixUnitWick_readout T a b c d

/-- A table obtained directly from a packet. -/
def ofPacket (P : FiveGradeBoundaryCurrentPacket L ι R) :
    FiveGradeCommutatorTable L ι R :=
  P

end FiveGradeCommutatorTable

end InfoGeometry.Canonical.ConformalFiveGradeCommutatorTable
