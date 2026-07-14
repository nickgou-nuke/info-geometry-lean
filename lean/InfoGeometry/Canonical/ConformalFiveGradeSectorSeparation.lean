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

namespace ConformalFiveGradeSectorSeparation

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
    ∀ x : L, x ∈ P.packet.sourceSet → x ∈ P.packet.sinkSet → False := by
  intro x hxsource hxsink
  have hneq : ConformalGrade.posTwo ≠ ConformalGrade.negTwo := by decide
  exact hneq (hxsource.symm.trans hxsink)

/-- The `+1` and `-1` sectors are disjoint. -/
theorem outgoing_incoming_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    ∀ x : L, x ∈ P.packet.inversion.outgoingSet →
      x ∈ P.packet.inversion.incomingSet → False := by
  intro x hxout hxin
  have hneq : ConformalGrade.posOne ≠ ConformalGrade.negOne := by decide
  exact hneq (hxout.symm.trans hxin)

/-- The source sector is disjoint from the modular center. -/
theorem source_center_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    ∀ x : L, x ∈ P.packet.sourceSet → x ∈ P.packet.centerSet → False := by
  intro x hxsource hxcenter
  have hneq : ConformalGrade.posTwo ≠ ConformalGrade.zero := by decide
  exact hneq (hxsource.symm.trans hxcenter)

/-- The sink sector is disjoint from the modular center. -/
theorem sink_center_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    ∀ x : L, x ∈ P.packet.sinkSet → x ∈ P.packet.centerSet → False := by
  intro x hxsink hxcenter
  have hneq : ConformalGrade.negTwo ≠ ConformalGrade.zero := by decide
  exact hneq (hxsink.symm.trans hxcenter)

/-- The source sector is disjoint from the outgoing boundary sector. -/
theorem source_outgoing_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    ∀ x : L, x ∈ P.packet.sourceSet →
      x ∈ P.packet.inversion.outgoingSet → False := by
  intro x hxsource hxout
  have hneq : ConformalGrade.posTwo ≠ ConformalGrade.posOne := by decide
  exact hneq (hxsource.symm.trans hxout)

/-- The sink sector is disjoint from the incoming boundary sector. -/
theorem sink_incoming_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    ∀ x : L, x ∈ P.packet.sinkSet →
      x ∈ P.packet.inversion.incomingSet → False := by
  intro x hxsink hxin
  have hneq : ConformalGrade.negTwo ≠ ConformalGrade.negOne := by decide
  exact hneq (hxsink.symm.trans hxin)

/-- The source sector is disjoint from the incoming boundary sector. -/
theorem source_incoming_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    ∀ x : L, x ∈ P.packet.sourceSet →
      x ∈ P.packet.inversion.incomingSet → False := by
  intro x hxsource hxin
  have hneq : ConformalGrade.posTwo ≠ ConformalGrade.negOne := by decide
  exact hneq (hxsource.symm.trans hxin)

/-- The sink sector is disjoint from the outgoing boundary sector. -/
theorem sink_outgoing_disjoint
    (P : FiveGradeSectorSeparationPacket L ι R) :
    ∀ x : L, x ∈ P.packet.sinkSet →
      x ∈ P.packet.inversion.outgoingSet → False := by
  intro x hxsink hxout
  have hneq : ConformalGrade.negTwo ≠ ConformalGrade.posOne := by decide
  exact hneq (hxsink.symm.trans hxout)

/-- A packet obtained directly from the current packet. -/
def ofPacket (P : FiveGradeBoundaryCurrentPacket L ι R) :
    FiveGradeSectorSeparationPacket L ι R where
  packet := P

end FiveGradeSectorSeparationPacket

end ConformalFiveGradeSectorSeparation
