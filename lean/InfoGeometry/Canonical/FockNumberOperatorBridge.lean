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
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.FockNumberOperatorBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Single-Mode Number Operator N_{α, u} = ε_α ∘ a_u on ExteriorAlgebra R (U →ₗ[R] R). -/
def singleModeNumberOp (alpha : U →ₗ[R] R) (u : U) (omega : ExteriorAlgebra R (U →ₗ[R] R)) : ExteriorAlgebra R (U →ₗ[R] R) :=
  creationOp alpha ((contractionOp (evaluationLinear u)) omega)

/-- **Theorem**: Single-Mode Number Operator Annihilates Vacuum State (N_{α, u} |0⟩ = 0). -/
theorem number_op_vacuum_zero (alpha : U →ₗ[R] R) (u : U) :
    singleModeNumberOp alpha u (vacuumState R U) = 0 := by
  simp only [singleModeNumberOp, annihilation_vacuum_zero, creationOp, mul_zero]

/-- Evaluated single-particle action of the actual number operator. -/
theorem number_op_single_particle_evaluated (alpha beta : U →ₗ[R] R) (u : U) :
    singleModeNumberOp alpha u (singleParticleState beta) =
      beta u • singleParticleState alpha := by
  simp only [singleModeNumberOp, single_particle_state_eq_generator,
    contraction_op_generator, creationOp, evaluation_linear_apply,
    Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm, mul_one]

/-- A normalized mode has the expected occupied-state eigenvalue one. -/
theorem number_op_occupied (alpha : U →ₗ[R] R) (u : U) (h : alpha u = 1) :
    singleModeNumberOp alpha u (singleParticleState alpha) = singleParticleState alpha := by
  rw [number_op_single_particle_evaluated, h, one_smul]

/-- The single-mode number operator satisfies its actual quadratic relation. -/
theorem number_op_square (alpha : U →ₗ[R] R) (u : U)
    (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    singleModeNumberOp alpha u (singleModeNumberOp alpha u omega) =
      alpha u • singleModeNumberOp alpha u omega := by
  simp only [singleModeNumberOp, creationOp, contraction_op_generator_mul,
    contraction_op_sq_zero, mul_zero, sub_zero, evaluation_linear_apply,
    Algebra.mul_smul_comm]

theorem number_op_idempotent (alpha : U →ₗ[R] R) (u : U) (h : alpha u = 1)
    (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    singleModeNumberOp alpha u (singleModeNumberOp alpha u omega) =
      singleModeNumberOp alpha u omega := by
  rw [number_op_square, h, one_smul]

/-- **Theorem**: Single-Mode Number Operator on Single-Particle State (N_{α, u} |β⟩ = ε_α (a_u |β⟩)). -/
theorem number_op_single_particle_action (alpha beta : U →ₗ[R] R) (u : U) :
    singleModeNumberOp alpha u (singleParticleState beta) =
    creationOp alpha ((contractionOp (evaluationLinear u)) (singleParticleState beta)) :=
  rfl

/-- **Theorem**: Master Fock Space Number Operator & State Spectrum Synthesis.
    Unifies:
    1. Single-mode number operator definition N_{α, u} = ε_α ∘ a_u.
    2. Vacuum state eigenvalue zero N_{α, u} |0⟩ = 0.
    3. Single-particle state action N_{α, u} |β⟩ = ε_α (a_u |β⟩). -/
theorem master_fock_number_operator_synthesis
    (alpha beta : U →ₗ[R] R) (u : U) :
    (singleModeNumberOp alpha u (vacuumState R U) = 0) ∧
    (singleModeNumberOp alpha u (singleParticleState beta) = creationOp alpha ((contractionOp (evaluationLinear u)) (singleParticleState beta))) := ⟨
  number_op_vacuum_zero alpha u,
  rfl
⟩

end InfoGeometry.Canonical.FockNumberOperatorBridge
