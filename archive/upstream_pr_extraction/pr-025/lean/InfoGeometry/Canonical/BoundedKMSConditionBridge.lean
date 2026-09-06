import InfoGeometry.Canonical.BoundedModularFlowCalibration
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.BoundedKMSConditionBridge

State-functional KMS carrier for the bounded Souriau/Drazin modular-flow
calibration.

This file uses the repository's `OperatorThermodynamics` theorem API:

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
state is a complex-valued functional with explicit positivity, normalization,
and normality propositions.  The KMS boundary law is currently owned by
`KMSAnalyticCertificate` for the bounded modular flow viewed as a plain
`FlowDatum`.
-/
@[rep_depth thermo]
structure Bridge where
  /-- Bounded Souriau/Drazin modular-flow calibration. -/
  boundedFlow :
    InfoGeometry.Canonical.BoundedModularFlowCalibration.Calibration
      (E := E) (LieAlgebra := LieAlgebra)

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
Minimal bounded KMS condition bridge.

This narrows the explicit `state` and bare `KMSAnalyticCertificate` fields to a
single `KMSState` for the bounded modular flow datum. The broader carrier
remains available through `toBridge`.
-/
@[rep_depth thermo]
structure MinimalBoundedKMSConditionBridge where
  /-- Bounded Souriau/Drazin modular-flow calibration. -/
  boundedFlow :
    InfoGeometry.Canonical.BoundedModularFlowCalibration.Calibration
      (E := E) (LieAlgebra := LieAlgebra)

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
    Bridge (E := E) (LieAlgebra := LieAlgebra) where
  boundedFlow := B.boundedFlow
  beta := B.beta
  state := B.kms.state
  kms := B.kms.kms

@[rep_depth thermo]
def toBridge :
    Bridge (E := E) (LieAlgebra := LieAlgebra) :=
  B.toBoundedKMSConditionBridge

/-- The legacy state field is definitionally the state carried by the KMS state. -/
@[rep_depth thermo]
theorem state_eq_kms_state :
    B.toBoundedKMSConditionBridge.state = B.kms.state :=
  rfl

/-- Backward-compatible name for the legacy bridge constructor. -/
@[rep_depth thermo]
theorem toBoundedKMSConditionBridge_state_eq :
    B.toBridge.state = B.kms.state :=
  rfl

/--
The integrated bounded KMS state also reconstructs the real-time invariance
surface definitionally, so downstream users on the minimal branch no longer
need to re-supply a separate `hInvariant` hypothesis.
-/
@[rep_depth thermo]
theorem flow_invariant
    (t : ℝ) (A : EndH) :
    B.kms.state.eval (B.boundedFlow.modularFlow.toFlowDatum.flow t A) =
      B.kms.state.eval A :=
  B.kms.flow_invariant_apply t A

/--
Read back the same real-time invariance statement on the legacy broad bounded
KMS bridge reconstructed from the integrated KMS state.
-/
@[rep_depth thermo]
theorem toBridge_flow_invariant
    (t : ℝ) (A : EndH) :
    B.toBridge.state.eval
        (B.boundedFlow.modularFlow.toFlowDatum.flow t A) =
      B.toBridge.state.eval A := by
  simpa [MinimalBoundedKMSConditionBridge.toBridge] using
    B.flow_invariant t A

end MinimalBoundedKMSConditionBridge

namespace Bridge

variable (B : Bridge (E := E) (LieAlgebra := LieAlgebra))

/-- The bounded modular flow as a plain operator-thermodynamic flow datum. -/
@[rep_depth thermo]
abbrev flowDatum :
    FlowDatum EndH :=
  B.boundedFlow.modularFlow.toFlowDatum

/-- The state evaluation signature used by the KMS carrier. -/
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

/-- Re-export the bounded KMS analytic boundary certificate. -/
@[rep_depth thermo]
theorem kms_boundary_holds :
    B.kms.boundaryCondition :=
  B.kms.boundaryCondition_holds

/--
Build the narrowed integrated KMS carrier from the broad bounded bridge once
real-time flow invariance is supplied explicitly.
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

/-- Legacy narrow-construction name retained for compatibility. -/
@[rep_depth thermo]
def toMinimal
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    MinimalBoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra) :=
  B.toMinimalBoundedKMSConditionBridge hInvariant

/-- The direct narrowed reverse route recovers the legacy state definitionally. -/
@[rep_depth thermo]
theorem toMinimalBoundedKMSConditionBridge_state_eq
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    (B.toMinimalBoundedKMSConditionBridge hInvariant).kms.state = B.state :=
  rfl

/-- Backward-compatible alias for callers using the shorter legacy name. -/
@[rep_depth thermo]
theorem toMinimal_state_eq
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    (B.toMinimal hInvariant).kms.state = B.state :=
  rfl

/-- The direct narrowed reverse route round-trips back to the broad bridge. -/
@[rep_depth thermo]
theorem toMinimalBoundedKMSConditionBridge_toBoundedKMSConditionBridge
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    (B.toMinimalBoundedKMSConditionBridge hInvariant).toBoundedKMSConditionBridge = B :=
  rfl

/-- Legacy theorem name for backwards compatibility. -/
@[rep_depth thermo]
theorem toMinimal_toBridge
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    (B.toMinimal hInvariant).toBridge = B :=
  rfl

/--
Compatibility theorem: build the narrowed integrated KMS carrier from the broad
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

/-- Legacy name kept for compatibility. -/
theorem toMinimal_of_flow_invariant
    (hInvariant :
      ∀ t : ℝ, ∀ A : EndH,
        B.state.eval (B.flowDatum.flow t A) = B.state.eval A) :
    ∃ M : MinimalBoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra),
      M.kms.state = B.state := by
  exact ⟨B.toMinimal hInvariant, rfl⟩

/--
The bounded KMS carrier inherits the Drazin regular-sector commutant stability
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

end Bridge

end Core

end InfoGeometry.Canonical.BoundedKMSConditionBridge
