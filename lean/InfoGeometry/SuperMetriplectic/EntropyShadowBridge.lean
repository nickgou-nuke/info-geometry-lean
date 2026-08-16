import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Meta.Architecture

/-!
# Native operator mismatch bridge

The former owner packaged scalar projector mismatch and body entropy fields.
The maintained statements are now made directly for an operator
`OperatorSchurDrazinBlock` on a `Ring`/`StarRing` carrier.
-/

namespace InfoGeometry.SuperMetriplectic.EntropyShadowBridge

open InfoGeometry.Canonical.MoorePenrose

variable {A : Type*} [Ring A] [StarRing A]

@[rep_depth operator]
theorem operator_projectorMismatch_eq_zero_iff
    (B : OperatorSchurDrazinBlock A) :
    projectorMismatch B.LΘΘ B.drazinElement B.penroseElement = 0 ↔
      spectralProjector B.LΘΘ B.drazinElement =
        metricProjector B.LΘΘ B.penroseElement := by
  exact projectorMismatch_eq_zero_iff

@[rep_depth operator]
theorem operator_chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero
    (B : OperatorSchurDrazinBlock A)
    (hΔ : projectorMismatch B.LΘΘ B.drazinElement B.penroseElement = 0) :
    chiralAnomaly B.LΘΘ B.drazinElement B.penroseElement = 0 := by
  exact chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero hΔ

@[rep_depth operator]
theorem operator_drazinDefectProjector_idempotent
    (B : OperatorSchurDrazinBlock A) :
    B.drazinDefectProjector * B.drazinDefectProjector =
      B.drazinDefectProjector := by
  exact B.drazinDefectProjector_idempotent

end InfoGeometry.SuperMetriplectic.EntropyShadowBridge
