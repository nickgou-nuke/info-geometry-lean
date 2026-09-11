import InfoGeometry.Canonical.ConformalFiveGradeSectorSeparation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.ConformalFiveGradeClosurePacket

Direct canonical closure packet for the five-grade conformal engine.

This file combines, on one direct canonical owner surface:

* the five-grade inversion carrier;
* the finite matrix-unit Wick current readout;
* the sector-separation facts for the extremal, boundary, and middle grades.

No bridge surface is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConformalFiveGradeClosurePacket

open InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket
open InfoGeometry.Canonical.ConformalFiveGradeSectorSeparation
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.ConformalFiveGradeInversion.FiveGradedConformalInversion
open InfoGeometry.Canonical.NormalOrderedCurrent

namespace FiveGradeClosurePacket

variable {L ι R : Type*}
variable [Fintype ι] [DecidableEq ι] [Ring R]

/-- Compatibility readouts for the direct canonical closure carrier. -/
def separation (P : FiveGradeBoundaryCurrentPacket L ι R) :
    FiveGradeBoundaryCurrentPacket L ι R :=
  P

/-- The commutator table readout of the closure packet. -/
theorem matrixUnitWick_readout
    (P : FiveGradeBoundaryCurrentPacket L ι R)
    (a b c d : ι) :
    algebraCommutator
        (normalOrderedMatrixUnit (R := R) P.occ a b)
        (normalOrderedMatrixUnit (R := R) P.occ c d)
      =
      (if b = c then normalOrderedMatrixUnit (R := R) P.occ a d else 0)
        - (if a = d then normalOrderedMatrixUnit (R := R) P.occ c b else 0)
        + wickCorrection (R := R) P.occ a b c d :=
  FiveGradeBoundaryCurrentPacket.matrixUnitWick_readout P a b c d

/-- The source sector is carried to the sink sector. -/
theorem source_to_sink
    (P : FiveGradeBoundaryCurrentPacket L ι R) (x : L) :
    x ∈ P.sourceSet ↔ P.inversion.theta x ∈ P.sinkSet :=
  FiveGradeBoundaryCurrentPacket.source_to_sink P x

/-- The incoming sector is carried to the outgoing sector. -/
theorem incoming_to_outgoing
    (P : FiveGradeBoundaryCurrentPacket L ι R) (x : L) :
    x ∈ P.inversion.incomingSet ↔
      P.inversion.theta x ∈ P.inversion.outgoingSet :=
  FiveGradeBoundaryCurrentPacket.incoming_to_outgoing P x

/-- The modular center remains stable under inversion. -/
theorem center_stable
    (P : FiveGradeBoundaryCurrentPacket L ι R) (x : L) :
    x ∈ P.centerSet ↔ P.inversion.theta x ∈ P.centerSet :=
  FiveGradeBoundaryCurrentPacket.center_stable P x

/-- The `+2` and `-2` sectors are disjoint. -/
theorem source_sink_disjoint
    (P : FiveGradeBoundaryCurrentPacket L ι R) :
    ∀ x : L, x ∈ P.sourceSet → x ∈ P.sinkSet → False :=
  FiveGradeSectorSeparationPacket.source_sink_disjoint P

/-- The `+1` and `-1` sectors are disjoint. -/
theorem outgoing_incoming_disjoint
    (P : FiveGradeBoundaryCurrentPacket L ι R) :
    ∀ x : L, x ∈ P.inversion.outgoingSet →
      x ∈ P.inversion.incomingSet → False :=
  FiveGradeSectorSeparationPacket.outgoing_incoming_disjoint P

/-- The source sector is disjoint from the modular center. -/
theorem source_center_disjoint
    (P : FiveGradeBoundaryCurrentPacket L ι R) :
    ∀ x : L, x ∈ P.sourceSet → x ∈ P.centerSet → False :=
  FiveGradeSectorSeparationPacket.source_center_disjoint P

/-- The sink sector is disjoint from the modular center. -/
theorem sink_center_disjoint
    (P : FiveGradeBoundaryCurrentPacket L ι R) :
    ∀ x : L, x ∈ P.sinkSet → x ∈ P.centerSet → False :=
  FiveGradeSectorSeparationPacket.sink_center_disjoint P

/-- The source sector is disjoint from the outgoing boundary sector. -/
theorem source_outgoing_disjoint
    (P : FiveGradeBoundaryCurrentPacket L ι R) :
    ∀ x : L, x ∈ P.sourceSet →
      x ∈ P.inversion.outgoingSet → False :=
  FiveGradeSectorSeparationPacket.source_outgoing_disjoint P

/-- The sink sector is disjoint from the incoming boundary sector. -/
theorem sink_incoming_disjoint
    (P : FiveGradeBoundaryCurrentPacket L ι R) :
    ∀ x : L, x ∈ P.sinkSet →
      x ∈ P.inversion.incomingSet → False :=
  FiveGradeSectorSeparationPacket.sink_incoming_disjoint P

/-- The source sector is disjoint from the incoming boundary sector. -/
theorem source_incoming_disjoint
    (P : FiveGradeBoundaryCurrentPacket L ι R) :
    ∀ x : L, x ∈ P.sourceSet →
      x ∈ P.inversion.incomingSet → False :=
  FiveGradeSectorSeparationPacket.source_incoming_disjoint P

/-- The sink sector is disjoint from the outgoing boundary sector. -/
theorem sink_outgoing_disjoint
    (P : FiveGradeBoundaryCurrentPacket L ι R) :
    ∀ x : L, x ∈ P.sinkSet →
      x ∈ P.inversion.outgoingSet → False :=
  FiveGradeSectorSeparationPacket.sink_outgoing_disjoint P

/-- A closure packet obtained directly from the current packet. -/
def ofCurrentPacket (P : FiveGradeBoundaryCurrentPacket L ι R) :
    FiveGradeBoundaryCurrentPacket L ι R :=
  P

end FiveGradeClosurePacket

end InfoGeometry.Canonical.ConformalFiveGradeClosurePacket
