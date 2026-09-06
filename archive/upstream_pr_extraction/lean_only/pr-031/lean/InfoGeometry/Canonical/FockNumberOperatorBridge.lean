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
  dsimp [singleModeNumberOp, creationOp, vacuumState, contractionOp]
  rw [mul_zero]

/-- **Theorem**: Single-Mode Number Operator on Single-Particle State (N_{α, u} |β⟩ = ε_α (a_u |β⟩)). -/
theorem number_op_single_particle_action (alpha beta : U →ₗ[R] R) (u : U) :
    singleModeNumberOp alpha u (singleParticleState beta) =
    creationOp alpha ((contractionOp (evaluationLinear u)) (singleParticleState beta)) :=
  rfl

/-- **Theorem**: Master Fock Space Number Operator & State Spectrum Synthesis.
    Unifies:
    1. Single-mode number operator definition N_{α, u} = ε_α ∘ a_u.
    2. Vacuum state eigenvalue zero N_{α, u} |0⟩ = 0.
    3. Single-particle state action N_{α, u} |β⟩ = ε_α (a_u |β⟩). -/
theorem master_fock_number_operator_synthesis
    (alpha beta : U →ₗ[R] R) (u : U) :
    (singleModeNumberOp alpha u (vacuumState R U) = 0) ∧
    (singleModeNumberOp alpha u (singleParticleState beta) = creationOp alpha ((contractionOp (evaluationLinear u)) (singleParticleState beta))) := ⟨
  number_op_vacuum_zero alpha u,
  rfl
⟩

end InfoGeometry.Canonical.FockNumberOperatorBridge
