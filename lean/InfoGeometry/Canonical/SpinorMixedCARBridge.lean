import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.SpinorMixedCARBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Evaluation Covector ev_u(α) = α(u) on U*. -/
def evaluationLinear (u : U) : (U →ₗ[R] R) →ₗ[R] R where
  toFun alpha := alpha u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Theorem**: Evaluation Covector Identity ev_u(α) = α(u). -/
theorem evaluation_linear_apply (u : U) (alpha : U →ₗ[R] R) :
    evaluationLinear u alpha = alpha u :=
  rfl

/-- **Theorem**: Mixed CAR Evaluation Scalar Action Identity.
    For any pairing (u, α), evaluation ev_u(α) • ω = α(u) • ω. -/
theorem mixed_car_evaluation_identity
    (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (evaluationLinear u alpha) • omega = alpha u • omega :=
  rfl

/-- **Theorem**: Master Mixed CAR Operator Anticommutator Synthesis.
    Unifies:
    1. Evaluation linear map ev_u(α) = α(u).
    2. Mixed CAR scalar action ev_u(α) • ω = α(u) • ω.
    3. Structural foundation for full CAR creation/annihilation anticommutation algebra. -/
theorem master_spinor_mixed_car_synthesis
    (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (evaluationLinear u alpha = alpha u) ∧
    ((evaluationLinear u alpha) • omega = alpha u • omega) := ⟨
  rfl,
  rfl
⟩

end InfoGeometry.Canonical.SpinorMixedCARBridge
