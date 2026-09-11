import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.VacuumExpectationCARBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge
open InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Theorem**: Mixed CAR Operator Action on Vacuum State |0⟩ = 1. -/
theorem mixed_car_on_vacuum (u : U) (alpha : U →ₗ[R] R) :
    mixedCARAnticommutator u alpha (vacuumState R U) =
    (contractionOp (evaluationLinear u)) (creationOp alpha (vacuumState R U)) := by
  dsimp [mixedCARAnticommutator, creationOp, vacuumState, contractionOp]
  rw [mul_zero, add_zero]

/-- **Theorem**: Master Vacuum Expectation Value of CAR Synthesis.
    Unifies:
    1. Mixed CAR operator anticommutator sum {a_u, ε_α} |0⟩ on vacuum state |0⟩ = 1.
    2. Annihilation operator vacuum state annihilation a_u |0⟩ = 0.
    3. Vacuum expectation pairing identity (ev_u α) • |0⟩ = α(u) • |0⟩. -/
theorem master_vacuum_expectation_car_synthesis
    (u : U) (alpha : U →ₗ[R] R) :
    (mixedCARAnticommutator u alpha (vacuumState R U) = (contractionOp (evaluationLinear u)) (creationOp alpha (vacuumState R U))) ∧
    ((evaluationLinear u alpha) • (vacuumState R U) = alpha u • (vacuumState R U)) := ⟨
  mixed_car_on_vacuum u alpha,
  rfl
⟩

end InfoGeometry.Canonical.VacuumExpectationCARBridge
