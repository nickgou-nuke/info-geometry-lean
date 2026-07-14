import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

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
`OperatorThermodynamics.KMSState`; this bridge does not duplicate those proof
fields.
-/

namespace HestenesAnalyticKMSBridge

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
-/
@[rep_depth krein]
structure Bridge where
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

  /-- Inverse temperature / period parameter for the existing KMS state. -/
  beta :
    ℝ

  /-- Existing operator-thermodynamic KMS certificate. -/
  kms :
    KMSState EndH flow beta

namespace Bridge

variable (B : Bridge (E := E))

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

/-- Readback: the underlying state is KMS relative to the operator flow. -/
@[rep_depth krein]
theorem kms_holds :
    B.kms.kms_boundary_condition :=
  B.kms.kms_boundary_condition_holds

/-- Readback: the underlying KMS state is invariant under the operator flow. -/
@[rep_depth krein]
theorem kms_flow_invariant
    (t : ℝ) (x : EndH) :
    B.kms.state.eval (B.flow.flow t x) = B.kms.state.eval x :=
  B.kms.flow_invariant t x

end Bridge

end Core

end HestenesAnalyticKMSBridge
