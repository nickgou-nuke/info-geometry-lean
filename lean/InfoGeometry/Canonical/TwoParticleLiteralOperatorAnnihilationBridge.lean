import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import InfoGeometry.Canonical.CrossAnticommutatorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.TwoParticleLiteralOperatorAnnihilationBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge
open InfoGeometry.Canonical.CrossAnticommutatorBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: 2-Particle Fock State |α ∧ β⟩ = ε_α |β⟩ in Exterior Algebra. -/
def twoParticleState (alpha beta : U →ₗ[R] R) : ExteriorAlgebra R (U →ₗ[R] R) :=
  creationOp alpha (singleParticleState beta)

/-- **Theorem**: Literal Operator 2-Particle Annihilation Identity a_u(|α ∧ β⟩) = α(u) • |β⟩ - β(u) • |α⟩.
    Under the CAR operator derivation law a_u(ε_α ω) = α(u) • ω - ε_α(a_u ω)
    and single-particle annihilation a_u |β⟩ = β(u) • |0⟩. -/
theorem annihilation_two_particle_operator_pairing
    (u : U) (alpha beta : U →ₗ[R] R)
    (a_u : ExteriorAlgebra R (U →ₗ[R] R) → ExteriorAlgebra R (U →ₗ[R] R))
    (h_car : ∀ (α : U →ₗ[R] R) (ω : ExteriorAlgebra R (U →ₗ[R] R)),
      a_u (creationOp α ω) = α u • ω - creationOp α (a_u ω))
    (h_single : a_u (singleParticleState beta) = beta u • vacuumState R U) :
    a_u (twoParticleState alpha beta) =
      alpha u • singleParticleState beta - beta u • singleParticleState alpha := by
  dsimp [twoParticleState]
  rw [h_car alpha (singleParticleState beta)]
  rw [h_single]
  dsimp [creationOp, singleParticleState, vacuumState]
  rw [Algebra.mul_smul_comm]

/-- **Theorem**: Master Literal Operator 2-Particle Annihilation Synthesis.
    Unifies:
    1. Definition of 2-particle Fock state |α ∧ β⟩ = ε_α |β⟩.
    2. CAR ladder derivation law a_u(ε_α ω) = α(u) • ω - ε_α(a_u ω).
    3. Single-particle state annihilation a_u |β⟩ = β(u) • |0⟩.
    4. Literal machine-checked operator theorem a_u(|α ∧ β⟩) = α(u) |β⟩ - β(u) |α⟩. -/
theorem master_two_particle_literal_operator_annihilation_synthesis
    (u : U) (alpha beta : U →ₗ[R] R)
    (a_u : ExteriorAlgebra R (U →ₗ[R] R) → ExteriorAlgebra R (U →ₗ[R] R))
    (h_car : ∀ (α : U →ₗ[R] R) (ω : ExteriorAlgebra R (U →ₗ[R] R)),
      a_u (creationOp α ω) = α u • ω - creationOp α (a_u ω))
    (h_single : a_u (singleParticleState beta) = beta u • vacuumState R U) :
    (a_u (twoParticleState alpha beta) =
      alpha u • singleParticleState beta - beta u • singleParticleState alpha) ∧
    (twoParticleState alpha beta = creationOp alpha (singleParticleState beta)) := by
  constructor
  · exact annihilation_two_particle_operator_pairing u alpha beta a_u h_car h_single
  · rfl

end InfoGeometry.Canonical.TwoParticleLiteralOperatorAnnihilationBridge
