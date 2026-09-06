import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Krein.HestenesAnalyticKMSBridge

Theorem-safe adapter separating three Hestenes--Krein structures:

* `K`-linearity / Hestenes analyticity: operators commute with the internal
  phase axis `clockAxis`;
* phase covariance of a supplied operator flow;
* the existing operator-thermodynamic KMS boundary certificate.

The file does not derive the analytic strip theorem from `K² = -1`.  The
ordinary KMS boundary remains the proof-carrying certificate owned by
`OperatorThermodynamics.KMSState`.
-/

namespace InfoGeometry.Krein.HestenesAnalyticKMSBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesRealStructures
open InfoGeometry.OperatorAlgebra.OperatorThermodynamics

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance instNormedRingEndH : NormedRing EndH := inferInstance
noncomputable local instance instNormedAlgebraRealEndH : NormedAlgebra ℝ EndH := inferInstance
local instance instTopologicalRingEndH : IsTopologicalRing EndH := inferInstance
local instance instCompleteSpaceEndH : CompleteSpace EndH := inferInstance

/--
Hestenes-analytic KMS adapter.

`K = clockAxis` is the internal real phase axis.  Hestenes analyticity of a
linear operator is `KLinear`, i.e. commutation with `K`.

The KMS analytic boundary is not derived here.  It is carried as an existing
`KMSState` certificate.
-/
@[rep_depth krein]
structure HestenesAnalyticKMSBridge where
  /-- Operator flow, e.g. a modular flow, on doubled real observables. -/
  flow :
    OperatorFlow EndH

  /-- The supplied flow preserves Hestenes analyticity / `K`-linearity. -/
  preserves_KLinear :
    ∀ t A,
      KLinear (E := E) A →
        KLinear (E := E) (flow.flow t A)

  /-- Strong left phase covariance: `σ_t(KA) = K σ_t(A)`. -/
  phase_left_covariant :
    ∀ t A,
      flow.flow t ((clockAxis (E := E)).comp A)
        =
      (clockAxis (E := E)).comp (flow.flow t A)

  /-- Strong right phase covariance: `σ_t(AK) = σ_t(A)K`. -/
  phase_right_covariant :
    ∀ t A,
      flow.flow t (A.comp (clockAxis (E := E)))
        =
      (flow.flow t A).comp (clockAxis (E := E))

  /-- Inverse temperature / period parameter for the existing KMS socket. -/
  beta :
    ℝ

  /-- Existing operator-thermodynamic KMS certificate. -/
  kms :
    KMSState EndH flow beta

/--
Constructive witness surface for the Hestenes-analytic KMS corridor.

This narrows the explicit `kms : KMSState ...` packet to the exact ingredients
used in this file: the underlying state, real-time invariance, and the analytic
boundary certificate, while preserving the flow-covariance owner data.
-/
@[rep_depth krein]
structure HestenesAnalyticKMSWitness where
  /-- Operator flow, e.g. a modular flow, on doubled real observables. -/
  flow :
    OperatorFlow EndH

  /-- The supplied flow preserves Hestenes analyticity / `K`-linearity. -/
  preserves_KLinear :
    ∀ t A,
      KLinear (E := E) A →
        KLinear (E := E) (flow.flow t A)

  /-- Strong left phase covariance: `σ_t(KA) = K σ_t(A)`. -/
  phase_left_covariant :
    ∀ t A,
      flow.flow t ((clockAxis (E := E)).comp A)
        =
      (clockAxis (E := E)).comp (flow.flow t A)

  /-- Strong right phase covariance: `σ_t(AK) = σ_t(A)K`. -/
  phase_right_covariant :
    ∀ t A,
      flow.flow t (A.comp (clockAxis (E := E)))
        =
      (flow.flow t A).comp (clockAxis (E := E))

  /-- Inverse temperature / period parameter for the existing KMS socket. -/
  beta : ℝ

  /-- Underlying state for the narrowed KMS witness route. -/
  state : AlgebraicState EndH

  /-- Real-time invariance of the state under the supplied flow. -/
  flow_invariant :
    ∀ t A, state.eval (flow.flow t A) = state.eval A

  /-- Analytic KMS strip-boundary proposition. -/
  kms_boundary_condition : Prop

  /-- Evidence for the analytic KMS strip-boundary proposition. -/
  kms_boundary_holds : kms_boundary_condition

namespace HestenesAnalyticKMSWitness

variable (W : HestenesAnalyticKMSWitness (E := E))

/-- Package the narrowed witness surface back into the legacy broad KMS bridge. -/
@[rep_depth krein]
def toBridge : HestenesAnalyticKMSBridge (E := E) where
  flow := W.flow
  preserves_KLinear := W.preserves_KLinear
  phase_left_covariant := W.phase_left_covariant
  phase_right_covariant := W.phase_right_covariant
  beta := W.beta
  kms := {
    state := W.state
    flow_invariant := W.flow_invariant
    kms_boundary_condition := W.kms_boundary_condition
    kms_boundary_condition_holds := W.kms_boundary_holds
  }

/-- The compatibility adapter reads back the same underlying state definitionally. -/
@[rep_depth krein]
theorem toBridge_state_eq :
    W.toBridge.kms.state = W.state :=
  rfl

/-- Route the legacy broad KMS bridge through a narrowed witness packet. -/
@[rep_depth krein]
theorem mk_broad_of_witness :
    ∃ B : HestenesAnalyticKMSBridge (E := E), B.kms.state = W.state :=
  ⟨W.toBridge, rfl⟩

end HestenesAnalyticKMSWitness

/-- Turn a legacy bridge into a narrowed witness structure by extracting the
underlying `KMSState` fields definitionally. This removes the explicit
`kms : KMSState ...` packet from the exposed surface on the witness route while
preserving the same owner data. -/
@[simp]
def HestenesAnalyticKMSBridge.fromBridge
    (B : HestenesAnalyticKMSBridge (E := E)) :
    HestenesAnalyticKMSWitness (E := E) where
  flow := B.flow
  preserves_KLinear := B.preserves_KLinear
  phase_left_covariant := B.phase_left_covariant
  phase_right_covariant := B.phase_right_covariant
  beta := B.beta
  state := B.kms.state
  flow_invariant := B.kms.flow_invariant
  kms_boundary_condition := B.kms.kms_boundary_condition
  kms_boundary_holds := B.kms.kms_boundary_condition_holds

/-- The bridge-to-witness conversion reads back the same state definitionally. -/
@[simp]
theorem HestenesAnalyticKMSBridge.fromBridge_state_eq
    (B : HestenesAnalyticKMSBridge (E := E)) :
    B.fromBridge.state = B.kms.state := by
  rfl

namespace HestenesAnalyticKMSBridge

variable (B : HestenesAnalyticKMSBridge (E := E))

/-- Readback: the flow preserves Hestenes analyticity / real complex-linearity. -/
@[rep_depth krein]
theorem flow_preserves_hestenes_analyticity
    (t : ℝ) (A : EndH)
    (hA : KLinear (E := E) A) :
    KLinear (E := E) (B.flow.flow t A) :=
  B.preserves_KLinear t A hA

/-- Readback: left multiplication by the internal phase axis is flow-covariant. -/
@[rep_depth krein]
theorem phase_left_covariance
    (t : ℝ) (A : EndH) :
    B.flow.flow t ((clockAxis (E := E)).comp A)
      =
    (clockAxis (E := E)).comp (B.flow.flow t A) :=
  B.phase_left_covariant t A

/-- Readback: right multiplication by the internal phase axis is flow-covariant. -/
@[rep_depth krein]
theorem phase_right_covariance
    (t : ℝ) (A : EndH) :
    B.flow.flow t (A.comp (clockAxis (E := E)))
      =
    (B.flow.flow t A).comp (clockAxis (E := E)) :=
  B.phase_right_covariant t A

/-- Readback: the KMS analytic-boundary certificate is available. -/
@[rep_depth thermo]
theorem kms_boundary_holds :
    B.kms.kms_boundary_condition :=
  B.kms.kms_boundary_condition_holds

/-- Readback: the KMS state is invariant under the supplied flow. -/
@[rep_depth thermo]
theorem kms_state_flow_invariant
    (t : ℝ) (A : EndH) :
    B.kms.state.eval (B.flow.flow t A) = B.kms.state.eval A :=
  B.kms.flow_invariant t A

end HestenesAnalyticKMSBridge

end Core

end InfoGeometry.Krein.HestenesAnalyticKMSBridge

end
