import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge
import InfoGeometry.Canonical.MixedCARCrossAlgebraBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.MixedCARFinalIdentityBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge
open InfoGeometry.Canonical.MixedCARCrossAlgebraBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Theorem**: Evaluation Functional Apply Identity ev_u(α) = α(u). -/
theorem evaluation_apply_identity (u : U) (alpha : U →ₗ[R] R) :
    evaluationLinear u alpha = alpha u :=
  rfl

/-- **Theorem**: Mixed CAR Final Scalar Action Identity (ev_u α • ω = α(u) • ω). -/
theorem mixed_car_final_scalar_identity (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (evaluationLinear u alpha) • omega = alpha u • omega :=
  rfl

end InfoGeometry.Canonical.MixedCARFinalIdentityBridge
