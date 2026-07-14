import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Canonical.NormalOrderedCurrent

/-!
# InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket

Direct canonical packet for the five-grade conformal inversion together with the
finite matrix-unit Wick readout.

This file stays in the canonical lane:

* the five-grade inversion carrier is imported directly;
* the normal-ordered matrix-unit commutator is imported directly;
* no bridge surface is introduced.

The packet is intentionally finite and local.  It packages the grade-swap
closure with the matrix-unit normal-ordering readout, without claiming any
new infinite current algebra construction.
-/

noncomputable section

namespace ConformalFiveGradeCurrentPacket

open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.ConformalFiveGradeInversion.FiveGradedConformalInversion
open InfoGeometry.Canonical.NormalOrderedCurrent

/--
Canonical packet combining the five-grade inversion carrier with the finite
matrix-unit Wick readout.

The grade inversion remains an abstract sector carrier, while the current law
is the direct matrix-unit normal-ordered commutator supplied by
`NormalOrderedCurrent`.
-/
structure FiveGradeBoundaryCurrentPacket
    (L : Type*) (ι : Type*) (R : Type*)
    [Fintype ι] [DecidableEq ι] [Ring R] where
  inversion : FiveGradedConformalInversion L
  occ : ι → ℤ
  matrixUnitWick :
    ∀ a b c d : ι,
      algebraCommutator
          (normalOrderedMatrixUnit (R := R) occ a b)
          (normalOrderedMatrixUnit (R := R) occ c d)
        =
        (if b = c then normalOrderedMatrixUnit (R := R) occ a d else 0)
          - (if a = d then normalOrderedMatrixUnit (R := R) occ c b else 0)
          + wickCorrection (R := R) occ a b c d

namespace FiveGradeBoundaryCurrentPacket

variable {L ι R : Type*}
variable [Fintype ι] [DecidableEq ι] [Ring R]

/-- The source sector of the packet's inversion carrier. -/
def sourceSet (P : FiveGradeBoundaryCurrentPacket L ι R) : Set L :=
  P.inversion.sourceSet

/-- The sink sector of the packet's inversion carrier. -/
def sinkSet (P : FiveGradeBoundaryCurrentPacket L ι R) : Set L :=
  P.inversion.sinkSet

/-- The modular center of the packet's inversion carrier. -/
def centerSet (P : FiveGradeBoundaryCurrentPacket L ι R) : Set L :=
  P.inversion.centerSet

/-- The packet readout is exactly the canonical finite matrix-unit Wick law. -/
theorem matrixUnitWick_readout
    (P : FiveGradeBoundaryCurrentPacket L ι R)
    (a b c d : ι) :
    algebraCommutator
        (normalOrderedMatrixUnit (R := R) P.occ a b)
        (normalOrderedMatrixUnit (R := R) P.occ c d)
      =
      (if b = c then normalOrderedMatrixUnit (R := R) P.occ a d else 0)
        - (if a = d then normalOrderedMatrixUnit (R := R) P.occ c b else 0)
        + wickCorrection (R := R) P.occ a b c d := by
  simpa using P.matrixUnitWick a b c d

/-- The source sector is carried to the sink sector by the packet inversion. -/
theorem source_to_sink
    (P : FiveGradeBoundaryCurrentPacket L ι R) (x : L) :
    x ∈ P.sourceSet ↔ P.inversion.theta x ∈ P.sinkSet := by
  simpa [sourceSet, sinkSet] using
    (mem_source_iff_mem_sink (G := P.inversion) x)

/-- The incoming sector is carried to the outgoing sector by the packet inversion. -/
theorem incoming_to_outgoing
    (P : FiveGradeBoundaryCurrentPacket L ι R) (x : L) :
    x ∈ P.inversion.incomingSet ↔ P.inversion.theta x ∈ P.inversion.outgoingSet := by
  simpa [incomingSet, outgoingSet] using
    (mem_incoming_iff_mem_outgoing (G := P.inversion) x)

/-- The modular center remains stable under inversion. -/
theorem center_stable
    (P : FiveGradeBoundaryCurrentPacket L ι R) (x : L) :
    x ∈ P.centerSet ↔ P.inversion.theta x ∈ P.centerSet := by
  simpa [centerSet] using (mem_center_iff_mem_center (G := P.inversion) x)

end FiveGradeBoundaryCurrentPacket

end ConformalFiveGradeCurrentPacket
