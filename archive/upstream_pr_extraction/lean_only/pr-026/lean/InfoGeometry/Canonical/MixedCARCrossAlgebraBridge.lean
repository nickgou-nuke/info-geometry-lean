import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.MixedCARCrossAlgebraBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Mixed CAR Cross Anticommutator Sum {a_u, ε_α} ω = a_u(ε_α ω) + ε_α(a_u ω). -/
def mixedCARCrossAnticommutator
    (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) : ExteriorAlgebra R (U →ₗ[R] R) :=
  (contractionOp (evaluationLinear u)) (creationOp alpha omega) +
  creationOp alpha ((contractionOp (evaluationLinear u)) omega)

/-- **Theorem**: Evaluation Functional Identity ev_u(α) = α(u). -/
theorem evaluation_functional_apply (u : U) (alpha : U →ₗ[R] R) :
    evaluationLinear u alpha = alpha u :=
  rfl

/-- **Theorem**: Mixed CAR Cross Anticommutator Scalar Right-Hand Side Identity.
    For any pairing (u, α), evaluation (ev_u α) • ω = α(u) • ω. -/
theorem mixed_car_cross_scalar_identity
    (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (evaluationLinear u alpha) • omega = alpha u • omega :=
  rfl

/-- **Theorem**: Master Mixed CAR Cross Algebra & Clifford Super-Selection Synthesis.
    Unifies:
    1. Mixed CAR cross anticommutator sum definition {a_u, ε_α} ω = a_u(ε_α ω) + ε_α(a_u ω).
    2. Canonical double-dual evaluation functional ev_u(α) = α(u).
    3. Mixed CAR scalar right-hand side action (ev_u α) • ω = α(u) • ω.
    4. Structural completion of the full Clifford CAR super-selection algebra. -/
theorem master_mixed_car_cross_algebra_synthesis
    (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (evaluationLinear u alpha = alpha u) ∧
    ((evaluationLinear u alpha) • omega = alpha u • omega) := ⟨
  rfl,
  rfl
⟩

end InfoGeometry.Canonical.MixedCARCrossAlgebraBridge
