import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.CARSpinorCliffordActionBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

open ExteriorAlgebra

/-- **Definition**: Creation Operator ε_α (ω) = α ∧ ω in ExteriorAlgebra R (Dual U). -/
def creationOp (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) : ExteriorAlgebra R (U →ₗ[R] R) :=
  ι R alpha * omega

/-- **Theorem**: Creation Operator Nilpotency ε_α(ε_α ω) = 0. -/
theorem creation_sq_zero (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    creationOp alpha (creationOp alpha omega) = 0 := by
  dsimp [creationOp]
  calc
    ι R alpha * (ι R alpha * omega) = (ι R alpha * ι R alpha) * omega := by noncomm_ring
    _ = 0 * omega := by rw [ExteriorAlgebra.ι_sq_zero (R:=R) alpha]
    _ = 0 := by noncomm_ring

/-- **Definition**: CAR Anticommutator for Creation and Contraction Operators. -/
def carOperatorAnticommutator
    (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R))
    (iota_u : ExteriorAlgebra R (U →ₗ[R] R) → ExteriorAlgebra R (U →ₗ[R] R)) : ExteriorAlgebra R (U →ₗ[R] R) :=
  iota_u (creationOp alpha omega) + creationOp alpha (iota_u omega)


end InfoGeometry.Canonical.CARSpinorCliffordActionBridge
