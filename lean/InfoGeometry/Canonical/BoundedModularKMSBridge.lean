import InfoGeometry.Canonical.BoundedModularFlowCalibration
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.BoundedModularKMSBridge

Adapter from the bounded modular-flow calibration layer to the existing
operator-algebraic KMS socket.

This file consumes:

* `BoundedModularFlowCalibration`, which calibrates an external flow against
  the bounded surrogate action;
* `OperatorThermodynamics.KMSState`, which carries the analytic KMS boundary
  condition as explicit witness data.

No analytic strip theorem is proved here. The KMS boundary condition remains a
certificate supplied by the model.

The purpose is to read back:

* invariance of the KMS state under the bounded calibrated flow;
* availability of the KMS analytic boundary certificate;
* compatibility of the bounded flow with `KsurAction`.
-/

namespace BoundedModularKMSBridge

open InfoGeometry.Canonical.BoundedModularFlowCalibration
open InfoGeometry.OperatorAlgebra.OperatorThermodynamics

section Core

variable {E LieAlgebra : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/--
KMS calibration for an already supplied bounded modular flow.

`operatorFlow` is the observable-level action used by the KMS owner.  It is
kept separate from `bounded.flow : ℝ → EndH`, which is the bounded
one-parameter operator family.
-/
@[rep_depth thermo]
structure Bridge where
  /-- Existing bounded-flow calibration owner. -/
  bounded :
    InfoGeometry.Canonical.BoundedModularFlowCalibration.Calibration
      (E := E) (LieAlgebra := LieAlgebra)

  /-- OperatorThermodynamics-compatible flow on observables. -/
  operatorFlow :
    OperatorFlow EndH

  /--
  Calibration of the `OperatorThermodynamics` flow to the ring-level modular
  automorphism flow carried by `BoundedModularFlowCalibration`.
  -/
  operatorFlow_eq_modularFlow :
    ∀ t : ℝ, ∀ A : EndH,
      operatorFlow.flow t A = bounded.modularFlow.flow t A

  /--
  Calibration of the observable flow to the bounded adjoint action
  `A ↦ U_t A U_{-t}`.
  -/
  operatorFlow_eq_bounded_adjoint :
    ∀ t : ℝ, ∀ A : EndH,
      operatorFlow.flow t A = bounded.flow t * A * bounded.flow (-t)

  /-- Inverse temperature. -/
  beta : ℝ

  /-- Supplied KMS state for the calibrated observable flow. -/
  kms :
    KMSState EndH operatorFlow beta

namespace Bridge

variable (B : Bridge (E := E) (LieAlgebra := LieAlgebra))

/-- The KMS state is invariant under the operator-flow action. -/
@[rep_depth thermo]
theorem kms_invariant_under_operatorFlow
    (t : ℝ) (A : EndH) :
    B.kms.state.eval (B.operatorFlow.flow t A) =
      B.kms.state.eval A :=
  B.kms.invariant t A

/--
The KMS state is invariant under the bounded adjoint action after applying the
flow calibration.
-/
@[rep_depth thermo]
theorem kms_invariant_under_bounded_adjoint_flow
    (t : ℝ) (A : EndH) :
    B.kms.state.eval (B.bounded.flow t * A * B.bounded.flow (-t)) =
      B.kms.state.eval A := by
  rw [← B.operatorFlow_eq_bounded_adjoint t A]
  exact B.kms_invariant_under_operatorFlow t A

/--
The KMS state is invariant under the ring-level modular automorphism flow from
`BoundedModularFlowCalibration`.
-/
@[rep_depth thermo]
theorem kms_invariant_under_bounded_modularFlow
    (t : ℝ) (A : EndH) :
    B.kms.state.eval (B.bounded.modularFlow.flow t A) =
      B.kms.state.eval A := by
  rw [← B.operatorFlow_eq_modularFlow t A]
  exact B.kms_invariant_under_operatorFlow t A

/-- The bounded flow is calibrated to the Drazin/MP surrogate action. -/
@[rep_depth thermo]
theorem bounded_flow_eq_exp_Ksur
    (t : ℝ) :
    B.bounded.flow t =
      NormedSpace.exp (t • B.bounded.souriau.superBridge.Ksur) :=
  B.bounded.flow_eq_exp_Ksur t

/-- The bounded flow is equivalently calibrated to the Souriau bare source. -/
@[rep_depth thermo]
theorem bounded_flow_eq_exp_Khat_beta
    (t : ℝ) :
    B.bounded.flow t =
      NormedSpace.exp (t • B.bounded.souriau.family.Khat_beta) :=
  B.bounded.flow_eq_exp_Khat_beta t

/-- Zero-time readback for the operator-flow owner. -/
@[rep_depth thermo]
theorem operatorFlow_zero
    (A : EndH) :
    B.operatorFlow.flow 0 A = A :=
  B.operatorFlow.flow_zero A

/-- Additive-time readback for the operator-flow owner. -/
@[rep_depth thermo]
theorem operatorFlow_add
    (s t : ℝ) (A : EndH) :
    B.operatorFlow.flow (s + t) A =
      B.operatorFlow.flow s (B.operatorFlow.flow t A) :=
  B.operatorFlow.flow_add s t A

/--
The KMS observable flow preserves the Drazin regular-sector commutant whenever
the underlying bounded modular-flow calibration fixes the Drazin regular
projector.
-/
@[rep_depth thermo]
theorem operatorFlow_preserves_commuting_with_spectralProjector
    (hFix : B.bounded.FlowFixesSpectralProjector)
    (A : EndH)
    (hComm :
      B.bounded.spectralProjector * A =
        A * B.bounded.spectralProjector)
    (t : ℝ) :
    B.bounded.spectralProjector * B.operatorFlow.flow t A =
      B.operatorFlow.flow t A * B.bounded.spectralProjector := by
  rw [B.operatorFlow_eq_modularFlow t A]
  exact
    B.bounded.modularFlow_preserves_commuting_with_spectralProjector
      hFix A hComm t

end Bridge

end Core

end BoundedModularKMSBridge
