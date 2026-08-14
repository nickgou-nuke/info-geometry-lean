import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.FockNumberOperatorBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Single-Mode Number Operator N_{α, u} = ε_α ∘ a_u on ExteriorAlgebra R (U →ₗ[R] R). -/
def singleModeNumberOp (alpha : U →ₗ[R] R) (u : U) (omega : ExteriorAlgebra R (U →ₗ[R] R)) : ExteriorAlgebra R (U →ₗ[R] R) :=
  creationOp alpha ((contractionOp (evaluationLinear u)) omega)

/-- **Theorem**: Single-Mode Number Operator Annihilates Vacuum State (N_{α, u} |0⟩ = 0). -/
theorem number_op_vacuum_zero (alpha : U →ₗ[R] R) (u : U) :
    singleModeNumberOp alpha u (vacuumState R U) = 0 := by
  change creationOp alpha
      (contractionOp (evaluationLinear u) (vacuumState R U)) = 0
  rw [annihilation_vacuum_zero]
  simp [creationOp]

/-- **Theorem**: Single-Mode Number Operator on Single-Particle State (N_{α, u} |β⟩ = ε_α (a_u |β⟩)). -/
theorem number_op_single_particle_action (alpha beta : U →ₗ[R] R) (u : U) :
    singleModeNumberOp alpha u (singleParticleState beta) =
    creationOp alpha ((contractionOp (evaluationLinear u)) (singleParticleState beta)) :=
  rfl

end InfoGeometry.Canonical.FockNumberOperatorBridge
