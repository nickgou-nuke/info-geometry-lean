import InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket

/-!
# InfoGeometry.Canonical.ConformalFiveGradeSectorSeparation

Direct canonical sector-separation layer for the five-grade conformal engine.

This file packages the separation facts that are already implicit in the
grade labels:

* the grade `±2` sectors are disjoint from each other;
* the grade `±2` sectors are disjoint from the boundary `±1` pair;
* the middle grade is separate from the extremal grades.

No bridge surface is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConformalFiveGradeSectorSeparation

open InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.ConformalFiveGradeInversion.FiveGradedConformalInversion

/--
Direct canonical sector-separation packet.

The packet combines the five-grade inversion carrier, the finite current
readout, and the disjointness facts separating extremal and boundary sectors.
-/
structure FiveGradeSectorSeparationPacket
    (L : Type*) (ι : Type*) (R : Type*)
    [Fintype ι] [DecidableEq ι] [Ring R] where
  packet : FiveGradeBoundaryCurrentPacket L ι R

namespace FiveGradeSectorSeparationPacket

variable {L ι R : Type*}
variable [Fintype ι] [DecidableEq ι] [Ring R]

/-- The `+2` and `-2` sectors are disjoint. -/
theorem source_sink_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    Disjoint P.packet.sourceSet P.packet.sinkSet := by
  intro x hxsource hxsink
  simp [FiveGradeBoundaryCurrentPacket.sourceSet,
    FiveGradeBoundaryCurrentPacket.sinkSet] at hxsource hxsink

/-- The `+1` and `-1` sectors are disjoint. -/
theorem outgoing_incoming_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    Disjoint P.packet.inversion.outgoingSet P.packet.inversion.incomingSet := by
  intro x hxout hxin
  simp [FiveGradeBoundaryCurrentPacket.outgoingSet,
    FiveGradeBoundaryCurrentPacket.incomingSet] at hxout hxin

/-- The source sector is disjoint from the modular center. -/
theorem source_center_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    Disjoint P.packet.sourceSet P.packet.centerSet := by
  intro x hxsource hxcenter
  simp [FiveGradeBoundaryCurrentPacket.sourceSet,
    FiveGradeBoundaryCurrentPacket.centerSet] at hxsource hxcenter

/-- The sink sector is disjoint from the modular center. -/
theorem sink_center_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    Disjoint P.packet.sinkSet P.packet.centerSet := by
  intro x hxsink hxcenter
  simp [FiveGradeBoundaryCurrentPacket.sinkSet,
    FiveGradeBoundaryCurrentPacket.centerSet] at hxsink hxcenter

/-- The source sector is disjoint from the outgoing boundary sector. -/
theorem source_outgoing_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    Disjoint P.packet.sourceSet P.packet.inversion.outgoingSet := by
  intro x hxsource hxout
  simp [FiveGradeBoundaryCurrentPacket.sourceSet,
    FiveGradeBoundaryCurrentPacket.outgoingSet] at hxsource hxout

/-- The sink sector is disjoint from the incoming boundary sector. -/
theorem sink_incoming_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    Disjoint P.packet.sinkSet P.packet.inversion.incomingSet := by
  intro x hxsink hxin
  simp [FiveGradeBoundaryCurrentPacket.sinkSet,
    FiveGradeBoundaryCurrentPacket.incomingSet] at hxsink hxin

/-- The source sector is disjoint from the incoming boundary sector. -/
theorem source_incoming_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    Disjoint P.packet.sourceSet P.packet.inversion.incomingSet := by
  intro x hxsource hxin
  simp [FiveGradeBoundaryCurrentPacket.sourceSet,
    FiveGradeBoundaryCurrentPacket.incomingSet] at hxsource hxin

/-- The sink sector is disjoint from the outgoing boundary sector. -/
theorem sink_outgoing_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    Disjoint P.packet.sinkSet P.packet.inversion.outgoingSet := by
  intro x hxsink hxout
  simp [FiveGradeBoundaryCurrentPacket.sinkSet,
    FiveGradeBoundaryCurrentPacket.outgoingSet] at hxsink hxout

/-- A packet obtained directly from the current packet. -/
def ofPacket (P : FiveGradeBoundaryCurrentPacket L ι R) :
    FiveGradeSectorSeparationPacket L ι R where
  packet := P

end FiveGradeSectorSeparationPacket

end InfoGeometry.Canonical.ConformalFiveGradeSectorSeparation
