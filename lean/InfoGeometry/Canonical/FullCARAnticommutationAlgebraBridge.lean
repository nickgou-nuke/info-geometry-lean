import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.FullCARAnticommutationAlgebraBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Theorem**: Creation-Creation CAR Anti-Commutativity {ε_α, ε_β} = 0. -/
theorem creation_creation_car_anticommute (alpha beta : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    creationOp alpha (creationOp beta omega) + creationOp beta (creationOp alpha omega) = 0 := by
  dsimp [creationOp]
  have h_add : ι R (alpha + beta) * ι R (alpha + beta) = 0 := ExteriorAlgebra.ι_sq_zero (R:=R) (alpha + beta)
  have h_a : ι R alpha * ι R alpha = 0 := ExteriorAlgebra.ι_sq_zero (R:=R) alpha
  have h_b : ι R beta * ι R beta = 0 := ExteriorAlgebra.ι_sq_zero (R:=R) beta
  rw [map_add] at h_add
  calc
    ι R alpha * (ι R beta * omega) + ι R beta * (ι R alpha * omega)
      = (ι R alpha * ι R beta + ι R beta * ι R alpha) * omega := by noncomm_ring
    _ = 0 * omega := by
      have h_ab : ι R alpha * ι R beta + ι R beta * ι R alpha = 0 := by
        calc ι R alpha * ι R beta + ι R beta * ι R alpha
          _ = (ι R alpha + ι R beta) * (ι R alpha + ι R beta) - ι R alpha * ι R alpha - ι R beta * ι R beta := by noncomm_ring
          _ = 0 - 0 - 0 := by rw [h_add, h_a, h_b]
          _ = 0 := by noncomm_ring
      rw [h_ab]
    _ = 0 := by noncomm_ring

/-- **Theorem**: Annihilation-Annihilation CAR Anti-Commutativity {a_u, a_v} = 0. -/
theorem annihilation_annihilation_car_anticommute (u v : U) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (contractionOp (evaluationLinear u)) ((contractionOp (evaluationLinear v)) omega) +
    (contractionOp (evaluationLinear v)) ((contractionOp (evaluationLinear u)) omega) = 0 :=
  contraction_op_anticommute (evaluationLinear u) (evaluationLinear v) omega


end InfoGeometry.Canonical.FullCARAnticommutationAlgebraBridge
