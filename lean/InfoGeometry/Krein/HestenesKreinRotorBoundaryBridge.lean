import InfoGeometry.Krein.HestenesModularKMSBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.HestenesKreinVacuumBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Krein.HestenesKreinRotorBoundaryBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesModularKMSBridge
open InfoGeometry.Krein.HestenesKreinVacuumBridge

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [KreinSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance instNormedRingEndH : NormedRing EndH := inferInstance
noncomputable local instance instNormedAlgebraRealEndH : NormedAlgebra ℝ EndH := inferInstance
local instance instTopologicalRingEndH : IsTopologicalRing EndH := inferInstance
local instance instCompleteSpaceEndH : CompleteSpace EndH := inferInstance

/--
Hestenes-Krein real rotor boundary.

This is the repo-native real boundary surface.  It intentionally avoids
claiming a complex KMS strip theorem.  The boundary is a supplied real
rotor/phase-periodicity law over the Hestenes-Krein packet.
-/
@[rep_depth krein]
def RealRotorBoundary
    (P : HestenesKreinKMSPacket (E := E))
    (period : ℝ)
    (realState : EndH → ℝ) : Prop :=
  ∀ A B : EndH, realState (A * (P.modularFlow.flow period B)) = realState (B * A)

/--
Compatibility bridge exposing the Hestenes-Krein thermal boundary as real
rotor periodicity rather than as a primitive complex-analytic KMS statement.

The existing `HestenesKreinKMSPacket` remains the implementation owner for
phase-axis compatibility and rotor conjugation.  This owner surface gives
downstream modules a KMS-free name for the same real boundary socket.
-/
@[rep_depth krein]
structure Bridge where
  /-- Real Hestenes-Krein packet with phase axis, rotor, and observable flow. -/
  packet :
    HestenesKreinKMSPacket (E := E)

  /-- Real rotor/thermal period. -/
  period :
    ℝ

  /-- Real state/readout used by the rotor boundary. -/
  realState :
    EndH → ℝ

  /-- Supplied real rotor boundary law. -/
  rotor_boundary_holds :
    RealRotorBoundary packet period realState

namespace Bridge

variable (B : Bridge (E := E))


/-- The phase axis squares to `-1` in the real operator algebra. -/
@[rep_depth krein]
theorem phaseAxis_sq :
    B.packet.phaseAxis * B.packet.phaseAxis = -(1 : EndH) :=
  B.packet.phaseAxis_sq

/-- The observable flow preserves Hestenes phase-axis compatibility. -/
@[rep_depth krein]
theorem flow_preserves_phaseAxis_left_action
    (t : ℝ) (A : EndH) :
    B.packet.modularFlow.flow t (B.packet.phaseAxis * A) =
      B.packet.phaseAxis * B.packet.modularFlow.flow t A :=
  B.packet.hestenes_flow_to_abstract_flow t A

/-- The observable flow is supplied by real rotor conjugation. -/
@[rep_depth krein]
theorem flow_eq_rotor_conjugation
    (t : ℝ) (A : EndH) :
    B.packet.modularFlow.flow t A =
      B.packet.rotor t * A * B.packet.rotorInv t :=
  B.packet.modularFlow_eq_rotor_conjugation_theorem t A

/-- The real rotor preserves the Krein null cone. -/
@[rep_depth krein]
theorem rotor_preserves_krein_null
    (t : ℝ) {ξ : E}
    (hξ : KreinSpace.kreinInner (H := E) ξ ξ = 0) :
    KreinSpace.kreinInner (H := E)
      (B.packet.rotor t ξ) (B.packet.rotor t ξ) = 0 :=
  B.packet.modular_rotor_preserves_null_cone t hξ

end Bridge

/--
Vacuum specialization of the Hestenes-Krein real rotor boundary.

This connects the rotor-boundary socket to the installed vacuum readout
`phi_Omega(A) = [A Omega, Omega]_J`.
-/
@[rep_depth krein]
structure HestenesKreinVacuumRotorBoundaryBridge
    (P : HestenesKreinKMSPacket (E := E)) where
  /-- Vacuum vector/readout carrier. -/
  vacuum :
    HestenesKreinVacuum P

  /-- Real rotor/thermal period. -/
  period :
    ℝ

  /-- Supplied real rotor boundary law for the vacuum readout. -/
  vacuum_rotor_boundary_holds :
    RealRotorBoundary P period vacuum.vacuumRealState

namespace HestenesKreinVacuumRotorBoundaryBridge

variable {P : HestenesKreinKMSPacket (E := E)}
variable (B : HestenesKreinVacuumRotorBoundaryBridge (E := E) P)


/-- Build the non-vacuum rotor-boundary bridge from the vacuum readout. -/
@[rep_depth krein]
def toRotorBoundaryBridge :
    Bridge (E := E) where
  packet := P
  period := B.period
  realState := B.vacuum.vacuumRealState
  rotor_boundary_holds := B.vacuum_rotor_boundary_holds


end HestenesKreinVacuumRotorBoundaryBridge

end Core

end InfoGeometry.Krein.HestenesKreinRotorBoundaryBridge
