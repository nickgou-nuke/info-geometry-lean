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

/-- **Theorem**: General Exterior Algebra 1-Form Generator Anticommutation (ι v ∧ ι w = - ι w ∧ ι v). -/
theorem exterior_generator_anticomm {V : Type*} [AddCommGroup V] [Module R V] (v w : V) :
    (ι R v : ExteriorAlgebra R V) * ι R w = - (ι R w * ι R v) := by
  have h_add : ι R (v + w) * ι R (v + w) = 0 := ExteriorAlgebra.ι_sq_zero (R:=R) (v + w)
  have h_v : ι R v * ι R v = 0 := ExteriorAlgebra.ι_sq_zero (R:=R) v
  have h_w : ι R w * ι R w = 0 := ExteriorAlgebra.ι_sq_zero (R:=R) w
  rw [map_add] at h_add
  have h : ι R v * ι R w + ι R w * ι R v = 0 := by
    calc ι R v * ι R w + ι R w * ι R v
      _ = (ι R v + ι R w) * (ι R v + ι R w) - ι R v * ι R v - ι R w * ι R w := by noncomm_ring
      _ = 0 - 0 - 0 := by rw [h_add, h_v, h_w]
      _ = 0 := by noncomm_ring
  exact eq_neg_of_add_eq_zero_left h

/-- **Theorem**: Two-Particle Fock State Anti-Symmetry (|α ∧ β⟩ = -|β ∧ α⟩). -/
theorem two_particle_state_antisymmetric (alpha beta : U →ₗ[R] R) :
    creationOp alpha (singleParticleState beta) = - creationOp beta (singleParticleState alpha) := by
  dsimp [creationOp, singleParticleState, vacuumState]
  rw [mul_one, mul_one]
  exact exterior_generator_anticomm alpha beta

end InfoGeometry.Canonical.SingleParticleFockStateBridge
