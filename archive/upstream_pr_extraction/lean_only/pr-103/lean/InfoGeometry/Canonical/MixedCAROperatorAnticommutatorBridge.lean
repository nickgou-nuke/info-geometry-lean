import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Mixed CAR Operator Anticommutator Sum {a_u, ε_α} ω = a_u(ε_α ω) + ε_α(a_u ω). -/
def mixedCARAnticommutator
    (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) : ExteriorAlgebra R (U →ₗ[R] R) :=
  (contractionOp (evaluationLinear u)) (creationOp alpha omega) +
  creationOp alpha ((contractionOp (evaluationLinear u)) omega)

/-- **Theorem**: Mixed CAR Evaluation Identity Bridge.
    Connects the evaluation linear functional ev_u(α) = α(u) to the scalar mixed CAR right-hand side α(u) • ω. -/
theorem mixed_car_evaluation_bridge (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (evaluationLinear u alpha) • omega = alpha u • omega :=
  rfl

end InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge
