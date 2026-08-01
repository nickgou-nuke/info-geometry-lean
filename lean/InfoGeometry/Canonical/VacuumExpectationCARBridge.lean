import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
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


end InfoGeometry.Canonical.VacuumExpectationCARBridge
