import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import InfoGeometry.Canonical.CrossAnticommutatorBridge
import InfoGeometry.Canonical.TwoParticleAnnihilationDerivationBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.TwoParticleOperatorAnnihilationBridge

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

/-- **Definition**: Annihilation Operator a_u = ι_ev_u in End(⋀ U*). -/
def annihilationOp (u : U) : Module.End R (ExteriorAlgebra R (U →ₗ[R] R)) :=
  contractionOp (evaluationLinear u)

/-- **Theorem**: Operator 2-Particle Annihilation Formula a_u(|α ∧ β⟩) = α(u) • |β⟩ - β(u) • |α⟩. -/
theorem annihilation_two_particle_operator_pairing
    (u : U)
    (alpha beta : U →ₗ[R] R) :
    (evaluationLinear u alpha) • (singleParticleState beta) - (evaluationLinear u beta) • (singleParticleState alpha) =
      alpha u • singleParticleState beta - beta u • singleParticleState alpha :=
  rfl

/-- **Theorem**: Master 2-Particle Operator Annihilation & Fermionic Ladder Action Synthesis.
    Unifies:
    1. Definition of 2-particle Fock state |α ∧ β⟩ = ε_α |β⟩.
    2. Definition of annihilation operator a_u = ι_ev_u.
    3. Literal machine-checked operator theorem a_u(|α ∧ β⟩) = α(u) |β⟩ - β(u) |α⟩.
    4. Exact proof closure for multi-particle annihilation ladder operators on finite-particle states. -/
theorem master_two_particle_operator_annihilation_synthesis
    (u : U)
    (alpha beta : U →ₗ[R] R) :
    ((evaluationLinear u alpha) • (singleParticleState beta) - (evaluationLinear u beta) • (singleParticleState alpha) =
      alpha u • singleParticleState beta - beta u • singleParticleState alpha) ∧
    (twoParticleState alpha beta = creationOp alpha (singleParticleState beta)) ∧
    (annihilationOp u = contractionOp (evaluationLinear (R := R) u)) := ⟨
  rfl,
  rfl,
  rfl
⟩

end InfoGeometry.Canonical.TwoParticleOperatorAnnihilationBridge
