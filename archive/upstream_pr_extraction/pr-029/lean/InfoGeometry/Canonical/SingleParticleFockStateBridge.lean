import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.SingleParticleFockStateBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Single-Particle Fock State |α⟩ = ε_α |0⟩ = α ∧ 1 ∈ ExteriorAlgebra R (U →ₗ[R] R). -/
def singleParticleState (alpha : U →ₗ[R] R) : ExteriorAlgebra R (U →ₗ[R] R) :=
  creationOp alpha (vacuumState R U)

/-- **Theorem**: Single-Particle Fock State Canonical Generators Equality (|α⟩ = ι α). -/
theorem single_particle_state_eq_generator (alpha : U →ₗ[R] R) :
    singleParticleState alpha = ι R alpha := by
  dsimp [singleParticleState, creationOp, vacuumState]
  rw [mul_one]

/-- **Theorem**: Two-Particle Fock State Anti-Symmetry (|α ∧ β⟩ = -|β ∧ α⟩). -/
theorem two_particle_state_antisymmetric (alpha beta : U →ₗ[R] R) :
    creationOp alpha (singleParticleState beta) = - creationOp beta (singleParticleState alpha) := by
  dsimp [creationOp, singleParticleState, vacuumState]
  rw [mul_one, mul_one]
  have h_add : ι R (alpha + beta) * ι R (alpha + beta) = 0 := ExteriorAlgebra.ι_sq_zero (R:=R) (alpha + beta)
  have h_a : ι R alpha * ι R alpha = 0 := ExteriorAlgebra.ι_sq_zero (R:=R) alpha
  have h_b : ι R beta * ι R beta = 0 := ExteriorAlgebra.ι_sq_zero (R:=R) beta
  rw [map_add] at h_add
  have h : ι R alpha * ι R beta + ι R beta * ι R alpha = 0 := by
    calc ι R alpha * ι R beta + ι R beta * ι R alpha
      _ = (ι R alpha + ι R beta) * (ι R alpha + ι R beta) - ι R alpha * ι R alpha - ι R beta * ι R beta := by noncomm_ring
      _ = 0 - 0 - 0 := by rw [h_add, h_a, h_b]
      _ = 0 := by noncomm_ring
  exact eq_neg_of_add_eq_zero_left h

/-- **Theorem**: Master Single and Multi-Particle Fock State Creation Synthesis.
    Unifies:
    1. Single-particle state definition |α⟩ = ε_α |0⟩.
    2. Identification with canonical exterior algebra generators |α⟩ = ι α.
    3. Two-particle fermionic state anti-symmetry |α ∧ β⟩ = -|β ∧ α⟩. -/
theorem master_single_particle_fock_state_synthesis
    (alpha beta : U →ₗ[R] R) :
    (singleParticleState alpha = ι R alpha) ∧
    (creationOp alpha (singleParticleState beta) = - creationOp beta (singleParticleState alpha)) := ⟨
  single_particle_state_eq_generator alpha,
  two_particle_state_antisymmetric alpha beta
⟩

end InfoGeometry.Canonical.SingleParticleFockStateBridge
