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
import InfoGeometry.Canonical.CrossAnticommutatorBridge
import InfoGeometry.Canonical.TwoParticleAnnihilationDerivationBridge
import Mathlib.Tactic.NoncommRing

/-!
# Actual contraction of a two-particle exterior state

The state and annihilation operator use the native exterior algebra of the
genuine dual. The action theorem follows from the contraction rule on a
generator product and evaluation on degree-one generators.
-/

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

/-- The two-particle exterior state obtained by two creation operations. -/
def twoParticleState (alpha beta : U →ₗ[R] R) : ExteriorAlgebra R (U →ₗ[R] R) :=
  creationOp alpha (singleParticleState beta)

/-- Native contraction by evaluation at the vector `u`. -/
def annihilationOp (u : U) : Module.End R (ExteriorAlgebra R (U →ₗ[R] R)) :=
  contractionOp (evaluationLinear u)

/-- Actual annihilation of a two-particle state, including its fermionic sign. -/
theorem annihilation_two_particle_action (u : U) (alpha beta : U →ₗ[R] R) :
    annihilationOp u (twoParticleState alpha beta) =
      alpha u • singleParticleState beta - beta u • singleParticleState alpha := by
  change contractionOp (evaluationLinear u) (ι R alpha * singleParticleState beta) =
    alpha u • singleParticleState beta - beta u • singleParticleState alpha
  rw [contraction_op_generator_mul]
  simp only [single_particle_state_eq_generator, contraction_on_generator,
    evaluation_linear_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

/-- Compatibility rewriting of the scalar evaluations appearing in the action formula. -/
theorem annihilation_two_particle_operator_pairing
    (u : U) (alpha beta : U →ₗ[R] R) :
    (evaluationLinear u alpha) • (singleParticleState beta) -
        (evaluationLinear u beta) • (singleParticleState alpha) =
      alpha u • singleParticleState beta - beta u • singleParticleState alpha :=
  rfl

/-- The original compatibility packet records evaluation rewriting and the two definitions. -/
theorem master_two_particle_operator_annihilation_synthesis
    (u : U) (alpha beta : U →ₗ[R] R) :
    ((evaluationLinear u alpha) • (singleParticleState beta) -
        (evaluationLinear u beta) • (singleParticleState alpha) =
      alpha u • singleParticleState beta - beta u • singleParticleState alpha) ∧
    (twoParticleState alpha beta = creationOp alpha (singleParticleState beta)) ∧
    (annihilationOp u = contractionOp (evaluationLinear (R := R) u)) :=
  ⟨rfl, rfl, rfl⟩

end InfoGeometry.Canonical.TwoParticleOperatorAnnihilationBridge
