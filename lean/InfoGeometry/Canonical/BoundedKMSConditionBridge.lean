import InfoGeometry.Canonical.BoundedModularFlowCalibration
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.BoundedKMSConditionBridge

State-functional KMS socket for the bounded Souriau/Drazin modular-flow
calibration.

This file uses the repository's `OperatorThermodynamics` witness API:

* `StateFunctional Op` carries `eval : Op → ℂ` plus positivity,
  normalization, and normality propositions.
* `KMSAnalyticCertificate σ β ω` carries the analytic strip/boundary condition
  as supplied evidence.

No finite-dimensional density matrix is introduced here, and no analytic KMS
theorem is inferred from the bounded flow alone.
-/

namespace InfoGeometry.Canonical.BoundedKMSConditionBridge

open InfoGeometry.Canonical.BoundedModularFlowCalibration
open InfoGeometry.OperatorAlgebra.Thermodynamics

section Core

variable {E LieAlgebra : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH :=
  inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH :=
  inferInstance
local instance : IsTopologicalRing EndH :=
  inferInstance
local instance : SMulCommClass ℝ EndH EndH :=
  inferInstance
local instance : IsScalarTower ℝ EndH EndH :=
  inferInstance

/--
Bounded KMS condition bridge.

The bounded flow owner supplies the calibrated ring-level modular flow.  The
state is a complex-valued functional with proof-carrying positivity,
normalization, and normality propositions.  The KMS boundary law is supplied
as a `KMSAnalyticCertificate` for the bounded modular flow viewed as a
plain `FlowDatum`.
-/
@[rep_depth thermo]
structure BoundedKMSConditionBridge where
  /-- Bounded Souriau/Drazin modular-flow calibration. -/
  boundedFlow :
    BoundedModularFlowCalibration (E := E) (LieAlgebra := LieAlgebra)

  /-- Inverse temperature. -/
  beta : ℝ

  /-- Complex-valued state/readout functional. -/
  state :
    StateFunctional EndH

  /-- KMS analytic certificate for the bounded surrogate modular flow. -/
  kms :
    KMSAnalyticCertificate
      boundedFlow.modularFlow.toFlowDatum
      beta
      state

/--
Constructive witness for the missing reverse-route ingredient on a broad bounded
KMS bridge.

The broad bridge already carries the state and analytic KMS certificate.  The
remaining datum needed to recover an integrated `KMSState` is explicit
real-time invariance of that state under the bounded modular flow.
-/
@[rep_depth thermo]
structure BoundedFlowInvariantStateWitness
    (B : BoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra)) where
  /-- Real-time invariance of the broad bridge state under the bounded flow datum. -/
  flow_invariant :
    ∀ t : ℝ, ∀ A : EndH,
      B.state.eval (B.boundedFlow.modularFlow.toFlowDatum.flow t A) = B.state.eval A

/--
Minimal bounded KMS condition bridge.

This narrows the explicit `state` and bare `KMSAnalyticCertificate` fields to a
single proof-carrying `KMSState` for the bounded modular flow datum. The legacy
broader packet remains available through `toBoundedKMSConditionBridge`.
-/
@[rep_depth thermo]
structure MinimalBoundedKMSConditionBridge where
  /-- Bounded Souriau/Drazin modular-flow calibration. -/
  boundedFlow :
    BoundedModularFlowCalibration (E := E) (LieAlgebra := LieAlgebra)

  /-- Inverse temperature. -/
  beta : ℝ

  /-- Integrated KMS state for the bounded modular flow datum. -/
  kms :
    KMSState EndH boundedFlow.modularFlow.toFlowDatum beta

namespace MinimalBoundedKMSConditionBridge

variable (B : MinimalBoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra))

/-- Recover the legacy broad bounded KMS bridge from the integrated KMS state. -/
@[rep_depth thermo]
def toBoundedKMSConditionBridge :
    BoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra) where
  boundedFlow := B.boundedFlow
  beta := B.beta
  state := B.kms.state
  kms := B.kms.kms

/-- The legacy state field is definitionally the state carried by the KMS socket. -/
@[rep_depth thermo]
theorem state_eq_kms_state :
    B.toBoundedKMSConditionBridge.state = B.kms.state :=
  rfl

/-- The analytic KMS boundary certificate is recovered from the integrated KMS state. -/
@[rep_depth thermo]
theorem kms_boundary_holds :
    B.toBoundedKMSConditionBridge.kms.boundaryCondition :=
  B.kms.kms_boundary_holds

end MinimalBoundedKMSConditionBridge

namespace BoundedKMSConditionBridge

variable (B : BoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra))

/-- The bounded modular flow as a plain operator-thermodynamic flow datum. -/
@[rep_depth thermo]
abbrev flowDatum :
    FlowDatum EndH :=
  B.boundedFlow.modularFlow.toFlowDatum

/-- The state evaluation signature used by the KMS socket. -/
@[rep_depth thermo]
abbrev eval : EndH → ℂ :=
  B.state.eval

/-- Readback: the flow datum is the bounded ring-level modular flow. -/
@[rep_depth thermo]
theorem flowDatum_apply
    (t : ℝ) (A : EndH) :
    B.flowDatum.flow t A = B.boundedFlow.modularFlow.flow t A :=
  rfl

/-- Readback: zero-time bounded KMS flow. -/
@[rep_depth thermo]
theorem flow_zero_apply
    (A : EndH) :
    B.flowDatum.flow 0 A = A :=
  B.boundedFlow.modularFlow.flow_zero A

/-- Readback: additive-time bounded KMS flow. -/
@[rep_depth thermo]
theorem flow_add_apply
    (s t : ℝ) (A : EndH) :
    B.flowDatum.flow (s + t) A =
      B.flowDatum.flow s (B.flowDatum.flow t A) :=
  B.boundedFlow.modularFlow.flow_add s t A

/-- Re-export the KMS analytic boundary condition. -/
@[rep_depth thermo]
theorem kms_boundary_holds :
    B.kms.boundaryCondition :=
  B.kms.boundaryCondition_holds

/--
Constructive reverse route: recover the narrowed integrated KMS packet from a
proof-carrying flow-invariance witness instead of a bare hypothesis argument.
-/
@[rep_depth thermo]
def toMinimalBoundedKMSConditionBridgeOfWitness
    (W : BoundedFlowInvariantStateWitness (E := E) (LieAlgebra := LieAlgebra) B) :
    MinimalBoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra) where
  boundedFlow := B.boundedFlow
  beta := B.beta
  kms := {
    state := B.state
    flow_invariant := W.flow_invariant
    kms := B.kms
  }

/-- The witness-routed reverse route recovers the legacy state definitionally. -/
@[rep_depth thermo]
theorem toMinimalBoundedKMSConditionBridgeOfWitness_state_eq
    (W : BoundedFlowInvariantStateWitness (E := E) (LieAlgebra := LieAlgebra) B) :
    (B.toMinimalBoundedKMSConditionBridgeOfWitness W).kms.state = B.state :=
  rfl

/-- The witness-routed reverse route round-trips back to the broad bridge. -/
@[rep_depth thermo]
theorem toMinimalBoundedKMSConditionBridgeOfWitness_toBoundedKMSConditionBridge
    (W : BoundedFlowInvariantStateWitness (E := E) (LieAlgebra := LieAlgebra) B) :
    (B.toMinimalBoundedKMSConditionBridgeOfWitness W).toBoundedKMSConditionBridge = B :=
  rfl

/--
Compatibility wrapper: build the narrowed integrated KMS packet from a broad
bridge using a proof-carrying flow-invariance witness.
-/
@[rep_depth thermo]
theorem toMinimalBoundedKMSConditionBridge_of_flow_invariant_witness
    (W : BoundedFlowInvariantStateWitness (E := E) (LieAlgebra := LieAlgebra) B) :
    ∃ M : MinimalBoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra),
      M.kms.state = B.state := by
  exact ⟨B.toMinimalBoundedKMSConditionBridgeOfWitness W, rfl⟩

/--
Build the narrowed integrated KMS packet from the broad bounded bridge once
real-time flow invariance is supplied explicitly.

This is the smallest honest reverse route currently available in this file:
the broad packet already carries the state and analytic KMS boundary witness,
but not the flow-invariance field required by `KMSState`.
-/
@[rep_depth thermo]
def toMinimalBoundedKMSConditionBridge
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    MinimalBoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra) where
  boundedFlow := B.boundedFlow
  beta := B.beta
  kms := {
    state := B.state
    flow_invariant := hInvariant
    kms := B.kms
  }

/-- The direct narrowed reverse route recovers the legacy state definitionally. -/
@[rep_depth thermo]
theorem toMinimalBoundedKMSConditionBridge_state_eq
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    (B.toMinimalBoundedKMSConditionBridge hInvariant).kms.state = B.state :=
  rfl

/-- The direct narrowed reverse route round-trips back to the broad bridge. -/
@[rep_depth thermo]
theorem toMinimalBoundedKMSConditionBridge_toBoundedKMSConditionBridge
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    (B.toMinimalBoundedKMSConditionBridge hInvariant).toBoundedKMSConditionBridge = B :=
  rfl

/--
Compatibility wrapper: build the narrowed integrated KMS packet from the broad
bounded bridge once real-time flow invariance is supplied explicitly.
-/
@[rep_depth thermo]
theorem toMinimalBoundedKMSConditionBridge_of_flow_invariant
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    ∃ M : MinimalBoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra),
      M.kms.state = B.state := by
  exact ⟨B.toMinimalBoundedKMSConditionBridge hInvariant, rfl⟩

/--
The bounded KMS socket inherits the Drazin regular-sector commutant stability
from the bounded modular-flow calibration when that flow fixes `P_D`.
-/
@[rep_depth thermo]
theorem flow_preserves_commuting_with_spectralProjector
    (hFix : B.boundedFlow.FlowFixesSpectralProjector)
    (A : EndH)
    (hComm :
      B.boundedFlow.spectralProjector * A =
        A * B.boundedFlow.spectralProjector)
    (t : ℝ) :
    B.boundedFlow.spectralProjector * B.flowDatum.flow t A =
      B.flowDatum.flow t A * B.boundedFlow.spectralProjector := by
  exact
    B.boundedFlow.modularFlow_preserves_commuting_with_spectralProjector
      hFix A hComm t

/--
The Massieu/partition-potential shift is compatible with the bounded KMS flow
when the bounded modular-flow owner is supplied with Souriau `opScale`
compatibility.
-/
@[rep_depth thermo]
theorem partition_potential_flow_central
    (hScale : B.boundedFlow.FlowCommutesWithOpScale)
    (t : ℝ) (A : EndH) :
    B.flowDatum.flow t
        (B.boundedFlow.souriau.family.opScale
          B.boundedFlow.souriau.family.partitionPotential A) =
      B.boundedFlow.souriau.family.opScale
        B.boundedFlow.souriau.family.partitionPotential
        (B.flowDatum.flow t A) :=
  B.boundedFlow.partition_potential_modularFlow_central hScale t A

end BoundedKMSConditionBridge

end Core

end InfoGeometry.Canonical.BoundedKMSConditionBridge
