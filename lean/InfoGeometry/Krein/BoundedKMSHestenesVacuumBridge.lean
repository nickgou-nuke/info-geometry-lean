import InfoGeometry.Krein.BoundedKMSHestenesBridge
import InfoGeometry.Krein.HestenesKreinVacuumBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Krein.BoundedKMSHestenesVacuumBridge

Adapter from the bounded KMS Hestenes real-form bridge to the existing
Hestenes/Krein vacuum-vector socket.

This is the point where the complex state-functional readout is identified
with a real Krein vacuum expectation `[AΩ, Ω]_J`, when such an `Ω` witness is
supplied.
-/

namespace InfoGeometry.Krein.BoundedKMSHestenesVacuumBridge

open InfoGeometry.Krein.BoundedKMSHestenesBridge
open InfoGeometry.Krein.HestenesKreinVacuumBridge

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
Bounded KMS Hestenes vacuum bridge.

`boundedHestenes` identifies the bounded KMS flow/state with the Hestenes real
packet.  `vacuum` supplies the standard real vacuum vector `Ω`.  The final
calibration states that the real shadow of the complex KMS functional is the
Krein vacuum expectation.
-/
@[rep_depth krein]
structure BoundedKMSHestenesVacuumBridge where
  /-- Bounded KMS to Hestenes real-form adapter. -/
  boundedHestenes :
    BoundedKMSHestenesBridge (E := E) (LieAlgebra := LieAlgebra)

  /-- Vacuum vector socket for the same Hestenes packet. -/
  vacuum :
    HestenesKreinVacuum boundedHestenes.hestenes

  /-- The bounded real state shadow is the Hestenes/Krein vacuum state. -/
  realState_eq_vacuumRealState :
    ∀ A : EndH, boundedHestenes.realState A = vacuum.vacuumRealState A

namespace BoundedKMSHestenesVacuumBridge

variable (B : BoundedKMSHestenesVacuumBridge (E := E) (LieAlgebra := LieAlgebra))

/-- Readback: bounded real state shadow equals the vacuum real state. -/
@[rep_depth krein]
theorem realState_eq_vacuumRealState_apply
    (A : EndH) :
    B.boundedHestenes.realState A = B.vacuum.vacuumRealState A :=
  B.realState_eq_vacuumRealState A

/-- The real part of the complex bounded KMS functional is the vacuum real state. -/
@[rep_depth krein]
theorem eval_re_eq_vacuumRealState
    (A : EndH) :
    (B.boundedHestenes.boundedKMS.state.eval A).re =
      B.vacuum.vacuumRealState A := by
  calc
    (B.boundedHestenes.boundedKMS.state.eval A).re
        = B.boundedHestenes.realState A := by
            rw [B.boundedHestenes.realState_eq_eval_re_apply A]
    _ = B.vacuum.vacuumRealState A :=
            B.realState_eq_vacuumRealState A

/-- The vacuum vector lies in the Hestenes/Krein natural cone. -/
@[rep_depth krein]
theorem vacuum_mem_naturalCone :
    B.vacuum.omega ∈ B.boundedHestenes.hestenes.HestenesNaturalCone :=
  B.vacuum.vacuum_mem_naturalCone

/-- The vacuum state is normalized on the identity observable. -/
@[rep_depth krein]
theorem vacuumRealState_id :
    B.vacuum.vacuumRealState (1 : EndH) = 1 :=
  B.vacuum.vacuumRealState_id

/-- The bounded real state shadow is normalized on the identity observable. -/
@[rep_depth krein]
theorem realState_id :
    B.boundedHestenes.realState (1 : EndH) = 1 := by
  rw [B.realState_eq_vacuumRealState_apply (1 : EndH)]
  exact B.vacuumRealState_id

/-- The Hestenes/Krein vacuum expectation is invariant under the real modular flow. -/
@[rep_depth krein]
theorem vacuumRealState_flow_invariant
    (t : ℝ) (A : EndH) :
    B.vacuum.vacuumRealState (B.boundedHestenes.hestenes.modularFlow.flow t A) =
      B.vacuum.vacuumRealState A :=
  B.vacuum.vacuumRealState_flow_invariant t A

/-- The bounded real state shadow is invariant under the Hestenes modular flow. -/
@[rep_depth krein]
theorem realState_flow_invariant
    (t : ℝ) (A : EndH) :
    B.boundedHestenes.realState
        (B.boundedHestenes.hestenes.modularFlow.flow t A) =
      B.boundedHestenes.realState A := by
  calc
    B.boundedHestenes.realState
        (B.boundedHestenes.hestenes.modularFlow.flow t A)
        = B.vacuum.vacuumRealState
            (B.boundedHestenes.hestenes.modularFlow.flow t A) := by
              rw [B.realState_eq_vacuumRealState_apply]
    _ = B.vacuum.vacuumRealState A :=
              B.vacuumRealState_flow_invariant t A
    _ = B.boundedHestenes.realState A := by
              rw [B.realState_eq_vacuumRealState_apply A]

/--
The Hestenes KMS boundary transported to the vacuum real state.
-/
@[rep_depth krein]
theorem vacuumRealState_kms_boundary
    (A C : EndH) :
    B.vacuum.vacuumRealState
        (A * (B.boundedHestenes.hestenes.modularFlow.flow
          B.boundedHestenes.boundedKMS.beta C)) =
      B.vacuum.vacuumRealState (C * A) := by
  calc
    B.vacuum.vacuumRealState
        (A * (B.boundedHestenes.hestenes.modularFlow.flow
          B.boundedHestenes.boundedKMS.beta C))
        = B.boundedHestenes.realState
            (A * (B.boundedHestenes.hestenes.modularFlow.flow
              B.boundedHestenes.boundedKMS.beta C)) := by
              rw [B.realState_eq_vacuumRealState_apply]
    _ = B.boundedHestenes.realState (C * A) :=
              B.boundedHestenes.hestenes_kms_boundary A C
    _ = B.vacuum.vacuumRealState (C * A) := by
              rw [B.realState_eq_vacuumRealState_apply]

end BoundedKMSHestenesVacuumBridge

end Core

end InfoGeometry.Krein.BoundedKMSHestenesVacuumBridge
