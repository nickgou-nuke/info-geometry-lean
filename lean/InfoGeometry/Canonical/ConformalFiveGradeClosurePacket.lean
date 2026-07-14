import InfoGeometry.Canonical.ConformalFiveGradeSectorSeparation

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

namespace ConformalFiveGradeClosurePacket

open InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket
open InfoGeometry.Canonical.ConformalFiveGradeSectorSeparation
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.ConformalFiveGradeInversion.FiveGradedConformalInversion
open InfoGeometry.Canonical.NormalOrderedCurrent

/--
Direct canonical closure packet for the conformal engine.

The packet stores the current boundary packet once, and all current/readout and
sector-separation data are read off from that single owner surface.
-/
structure FiveGradeClosurePacket
    (L : Type*) (ι : Type*) (R : Type*)
    [Fintype ι] [DecidableEq ι] [Ring R] where
  packet : FiveGradeBoundaryCurrentPacket L ι R
  separation : FiveGradeSectorSeparationPacket L ι R
  separation_packet_eq : separation.packet = packet

namespace FiveGradeClosurePacket

variable {L ι R : Type*}
variable [Fintype ι] [DecidableEq ι] [Ring R]

/-- The commutator table readout of the closure packet. -/
theorem matrixUnitWick_readout
    (P : FiveGradeClosurePacket L ι R)
    (a b c d : ι) :
    algebraCommutator
        (normalOrderedMatrixUnit (R := R) P.packet.occ a b)
        (normalOrderedMatrixUnit (R := R) P.packet.occ c d)
      =
      (if b = c then normalOrderedMatrixUnit (R := R) P.packet.occ a d else 0)
        - (if a = d then normalOrderedMatrixUnit (R := R) P.packet.occ c b else 0)
        + wickCorrection (R := R) P.packet.occ a b c d :=
  P.packet.matrixUnitWick_readout a b c d

/-- The source sector is carried to the sink sector. -/
theorem source_to_sink
    (P : FiveGradeClosurePacket L ι R) (x : L) :
    x ∈ P.packet.sourceSet ↔ P.packet.inversion.theta x ∈ P.packet.sinkSet :=
  P.packet.source_to_sink x

/-- The incoming sector is carried to the outgoing sector. -/
theorem incoming_to_outgoing
    (P : FiveGradeClosurePacket L ι R) (x : L) :
    x ∈ P.packet.inversion.incomingSet ↔
      P.packet.inversion.theta x ∈ P.packet.inversion.outgoingSet :=
  P.packet.incoming_to_outgoing x

/-- The modular center remains stable under inversion. -/
theorem center_stable
    (P : FiveGradeClosurePacket L ι R) (x : L) :
    x ∈ P.packet.centerSet ↔ P.packet.inversion.theta x ∈ P.packet.centerSet :=
  P.packet.center_stable x

/-- The `+2` and `-2` sectors are disjoint. -/
theorem source_sink_disjoint
    (P : FiveGradeClosurePacket L ι R) :
    ∀ x : L, x ∈ P.packet.sourceSet → x ∈ P.packet.sinkSet → False :=
  by
    simpa [P.separation_packet_eq] using
      (FiveGradeSectorSeparationPacket.source_sink_disjoint P.separation)

/-- The `+1` and `-1` sectors are disjoint. -/
theorem outgoing_incoming_disjoint
    (P : FiveGradeClosurePacket L ι R) :
    ∀ x : L, x ∈ P.packet.inversion.outgoingSet →
      x ∈ P.packet.inversion.incomingSet → False :=
  by
    simpa [P.separation_packet_eq] using
      (FiveGradeSectorSeparationPacket.outgoing_incoming_disjoint P.separation)

/-- The source sector is disjoint from the modular center. -/
theorem source_center_disjoint
    (P : FiveGradeClosurePacket L ι R) :
    ∀ x : L, x ∈ P.packet.sourceSet → x ∈ P.packet.centerSet → False :=
  by
    simpa [P.separation_packet_eq] using
      (FiveGradeSectorSeparationPacket.source_center_disjoint P.separation)

/-- The sink sector is disjoint from the modular center. -/
theorem sink_center_disjoint
    (P : FiveGradeClosurePacket L ι R) :
    ∀ x : L, x ∈ P.packet.sinkSet → x ∈ P.packet.centerSet → False :=
  by
    simpa [P.separation_packet_eq] using
      (FiveGradeSectorSeparationPacket.sink_center_disjoint P.separation)

/-- The source sector is disjoint from the outgoing boundary sector. -/
theorem source_outgoing_disjoint
    (P : FiveGradeClosurePacket L ι R) :
    ∀ x : L, x ∈ P.packet.sourceSet →
      x ∈ P.packet.inversion.outgoingSet → False :=
  by
    simpa [P.separation_packet_eq] using
      (FiveGradeSectorSeparationPacket.source_outgoing_disjoint P.separation)

/-- The sink sector is disjoint from the incoming boundary sector. -/
theorem sink_incoming_disjoint
    (P : FiveGradeClosurePacket L ι R) :
    ∀ x : L, x ∈ P.packet.sinkSet →
      x ∈ P.packet.inversion.incomingSet → False :=
  by
    simpa [P.separation_packet_eq] using
      (FiveGradeSectorSeparationPacket.sink_incoming_disjoint P.separation)

/-- The source sector is disjoint from the incoming boundary sector. -/
theorem source_incoming_disjoint
    (P : FiveGradeClosurePacket L ι R) :
    ∀ x : L, x ∈ P.packet.sourceSet →
      x ∈ P.packet.inversion.incomingSet → False :=
  by
    simpa [P.separation_packet_eq] using
      (FiveGradeSectorSeparationPacket.source_incoming_disjoint P.separation)

/-- The sink sector is disjoint from the outgoing boundary sector. -/
theorem sink_outgoing_disjoint
    (P : FiveGradeClosurePacket L ι R) :
    ∀ x : L, x ∈ P.packet.sinkSet →
      x ∈ P.packet.inversion.outgoingSet → False :=
  by
    simpa [P.separation_packet_eq] using
      (FiveGradeSectorSeparationPacket.sink_outgoing_disjoint P.separation)

/-- A closure packet obtained directly from the current packet. -/
def ofCurrentPacket (P : FiveGradeBoundaryCurrentPacket L ι R) :
    FiveGradeClosurePacket L ι R where
  packet := P
  separation := FiveGradeSectorSeparationPacket.ofPacket P
  separation_packet_eq := rfl

end FiveGradeClosurePacket

end ConformalFiveGradeClosurePacket
