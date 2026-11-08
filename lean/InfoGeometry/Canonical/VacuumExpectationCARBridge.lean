/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

/-- On the vacuum the reverse-ordered term vanishes by native annihilation. -/
theorem mixed_car_on_vacuum (u : U) (alpha : U →ₗ[R] R) :
    mixedCARAnticommutator u alpha (vacuumState R U) =
    (contractionOp (evaluationLinear u)) (creationOp alpha (vacuumState R U)) := by
  unfold mixedCARAnticommutator
  rw [annihilation_vacuum_zero]
  simp only [creationOp, mul_zero, add_zero]

/-- The actual mixed CAR evaluates to the scalar pairing times the vacuum. -/
theorem mixed_car_vacuum_evaluation (u : U) (alpha : U →ₗ[R] R) :
    mixedCARAnticommutator u alpha (vacuumState R U) =
      alpha u • vacuumState R U :=
  mixed_car_operator_identity u alpha (vacuumState R U)

/-- The original vacuum/evaluation compatibility packet retains its statement. -/
theorem master_vacuum_expectation_car_synthesis
    (u : U) (alpha : U →ₗ[R] R) :
    (mixedCARAnticommutator u alpha (vacuumState R U) =
      (contractionOp (evaluationLinear u)) (creationOp alpha (vacuumState R U))) ∧
    ((evaluationLinear u alpha) • (vacuumState R U) =
      alpha u • (vacuumState R U)) :=
  ⟨mixed_car_on_vacuum u alpha, rfl⟩

end InfoGeometry.Canonical.VacuumExpectationCARBridge
