import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.VacuumExpectationValueBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Theorem**: Single-Particle State Creation on Vacuum (|α⟩ = ε_α |0⟩ = ι α). -/
theorem single_particle_creation_vacuum (alpha : U →ₗ[R] R) :
    creationOp alpha (vacuumState R U) = ι R alpha := by
  dsimp [creationOp, vacuumState]
  rw [mul_one]

/-- **Theorem**: Annihilation Operator Annihilates Vacuum (a_u |0⟩ = 0). -/
theorem annihilation_vacuum_is_zero (u : U) :
    (contractionOp (evaluationLinear u)) (vacuumState R U) = 0 :=
  annihilation_vacuum_zero u

/-- **Theorem**: Vacuum Expectation Value Pairing (ev_u α • |0⟩ = α(u) • |0⟩). -/
theorem vacuum_expectation_value_pairing (u : U) (alpha : U →ₗ[R] R) :
    (evaluationLinear u alpha) • (vacuumState R U) = alpha u • (vacuumState R U) :=
  rfl

/-- **Theorem**: Master Vacuum Expectation Value & State Pairing Synthesis.
    Unifies:
    1. Single-particle state creation on vacuum |α⟩ = ε_α |0⟩ = ι α.
    2. Vacuum state annihilation a_u |0⟩ = 0 for all u ∈ U.
    3. Vacuum expectation pairing identity (ev_u α) • |0⟩ = α(u) • |0⟩. -/
theorem master_vacuum_expectation_value_synthesis
    (u : U) (alpha : U →ₗ[R] R) :
    (creationOp alpha (vacuumState R U) = ι R alpha) ∧
    ((contractionOp (evaluationLinear u)) (vacuumState R U) = 0) ∧
    ((evaluationLinear u alpha) • (vacuumState R U) = alpha u • (vacuumState R U)) := ⟨
  single_particle_creation_vacuum alpha,
  annihilation_vacuum_is_zero u,
  rfl
⟩

end InfoGeometry.Canonical.VacuumExpectationValueBridge
