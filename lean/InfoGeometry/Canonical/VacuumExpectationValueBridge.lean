import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
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

end InfoGeometry.Canonical.VacuumExpectationValueBridge
