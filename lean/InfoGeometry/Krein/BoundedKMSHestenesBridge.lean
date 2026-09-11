import InfoGeometry.Canonical.BoundedKMSConditionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.HestenesModularKMSBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Krein.BoundedKMSHestenesBridge

Adapter from the bounded Souriau/Drazin KMS socket to the existing
Hestenes/Krein real-form KMS packet.

This file does not reprove the analytic KMS strip theorem, and it does not
construct the Hestenes rotor.  It records the calibration data needed to read
the bounded modular flow as a real Hestenes/Krein modular rotor flow.
-/

namespace InfoGeometry.Krein.BoundedKMSHestenes

open InfoGeometry.Canonical.BoundedKMSConditionBridge
open InfoGeometry.Krein.HestenesModularKMSBridge
open InfoGeometry.OperatorAlgebra.OperatorThermodynamics
open InfoGeometry.OperatorAlgebra.Thermodynamics

section Core

variable {E LieAlgebra : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [KreinSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH :=
  inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH :=
  inferInstance
local instance : IsTopologicalRing EndH :=
  inferInstance
local instance : CompleteSpace EndH :=
  inferInstance
local instance : SMulCommClass ℝ EndH EndH :=
  inferInstance
local instance : IsScalarTower ℝ EndH EndH :=
  inferInstance

/--
Bounded KMS to Hestenes/Krein real-form bridge.

The complex-valued bounded KMS state remains the owner of the abstract analytic
certificate.  The Hestenes packet supplies the real phase axis, rotor
implementation, and Krein-cone preservation.  The equality field identifies
the Hestenes observable flow with the bounded modular flow datum.
-/
@[rep_depth krein]
structure BoundedKMSHestenesBridge where
  /-- Bounded Souriau/Drazin state-functional KMS socket. -/
  boundedKMS :
    InfoGeometry.Canonical.BoundedKMSConditionBridge.Bridge
      (E := E) (LieAlgebra := LieAlgebra)

  /-- Hestenes/Krein real-form modular packet. -/
  hestenes :
    HestenesKreinKMSPacket (E := E)

  /-- The Hestenes observable flow is the bounded modular flow. -/
  hestenesFlow_eq_boundedFlow :
    ∀ (t : ℝ) (A : EndH),
      hestenes.modularFlow.flow t A = boundedKMS.flowDatum.flow t A

  /-- Real shadow of the complex KMS state. -/
  realState :
    EndH → ℝ

  /-- The real shadow is the real part of the bounded KMS functional. -/
  realState_eq_eval_re :
    ∀ A : EndH, realState A = (boundedKMS.state.eval A).re

  /--
  Hestenes real-form KMS boundary witness.

  This is intentionally explicit: the complex analytic certificate is a
  witness-level proposition in the operator-thermodynamic API, not a concrete
  formula from which the real boundary law can be unfolded automatically.
  -/
  hestenesKMS :
    hestenes.IsHestenesKMSCondition boundedKMS.beta realState

namespace BoundedKMSHestenesBridge

variable (B : BoundedKMSHestenesBridge (E := E) (LieAlgebra := LieAlgebra))

/-- Readback: Hestenes observable flow equals the bounded modular flow datum. -/
@[rep_depth krein]
theorem hestenesFlow_eq_boundedFlow_apply
    (t : ℝ) (A : EndH) :
    B.hestenes.modularFlow.flow t A = B.boundedKMS.flowDatum.flow t A :=
  B.hestenesFlow_eq_boundedFlow t A

/-- Readback: the real Hestenes state is the real part of the complex KMS state. -/
@[rep_depth krein]
theorem realState_eq_eval_re_apply
    (A : EndH) :
    B.realState A = (B.boundedKMS.state.eval A).re :=
  B.realState_eq_eval_re A

/-- Re-export the bounded complex KMS analytic certificate. -/
@[rep_depth krein]
theorem bounded_kms_boundary_holds :
    B.boundedKMS.kms.boundaryCondition :=
  B.boundedKMS.kms_boundary_holds

/-- Re-export the Hestenes real-form KMS boundary law. -/
@[rep_depth krein]
theorem hestenes_kms_boundary
    (A C : EndH) :
    B.realState (A * (B.hestenes.modularFlow.flow B.boundedKMS.beta C)) =
      B.realState (C * A) :=
  B.hestenesKMS A C

/--
The Hestenes flow preserves Drazin regular-sector commutation whenever the
bounded modular flow fixes the Drazin regular projector.
-/
@[rep_depth krein]
theorem hestenesFlow_preserves_commuting_with_spectralProjector
    (hFix : B.boundedKMS.boundedFlow.FlowFixesSpectralProjector)
    (A : EndH)
    (hComm :
      B.boundedKMS.boundedFlow.spectralProjector * A =
        A * B.boundedKMS.boundedFlow.spectralProjector)
    (t : ℝ) :
    B.boundedKMS.boundedFlow.spectralProjector *
        B.hestenes.modularFlow.flow t A =
      B.hestenes.modularFlow.flow t A *
        B.boundedKMS.boundedFlow.spectralProjector := by
  rw [B.hestenesFlow_eq_boundedFlow_apply t A]
  exact
    B.boundedKMS.flow_preserves_commuting_with_spectralProjector
      hFix A hComm t

/-- The Hestenes rotor preserves the Krein natural cone. -/
@[rep_depth krein]
theorem rotor_preserves_HestenesNaturalCone
    (t : ℝ) {ξ : E}
    (hξ : ξ ∈ B.hestenes.HestenesNaturalCone) :
    B.hestenes.rotor t ξ ∈ B.hestenes.HestenesNaturalCone :=
  B.hestenes.rotor_preserves_HestenesNaturalCone t hξ

/-- The Hestenes rotor preserves the Krein null cone. -/
@[rep_depth krein]
theorem modular_rotor_preserves_null_cone
    (t : ℝ) {ξ : E}
    (hNull : KreinSpace.kreinInner (H := E) ξ ξ = 0) :
    KreinSpace.kreinInner (H := E)
        (B.hestenes.rotor t ξ) (B.hestenes.rotor t ξ) = 0 :=
  B.hestenes.modular_rotor_preserves_null_cone t hNull

end BoundedKMSHestenesBridge

end Core

end InfoGeometry.Krein.BoundedKMSHestenes
