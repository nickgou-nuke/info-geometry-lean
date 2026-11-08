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

/-!
# Occupation on the native exterior Fock carrier

For a covector `alpha` and vector `u`, the operator is exterior creation composed
with genuine contraction. Its square is `(alpha u)` times itself. Thus the
normalization `alpha u = 1` gives an actual nonzero occupation projector.
-/

noncomputable section

namespace InfoGeometry.Canonical.FockNumberOperatorBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- Single-mode occupation, using exterior creation and native contraction. -/
def singleModeNumberOp (alpha : U →ₗ[R] R) (u : U)
    (omega : ExteriorAlgebra R (U →ₗ[R] R)) : ExteriorAlgebra R (U →ₗ[R] R) :=
  creationOp alpha ((contractionOp (evaluationLinear u)) omega)

/-- The same occupation operator in the endomorphism algebra. -/
def singleModeNumberEnd (alpha : U →ₗ[R] R) (u : U) :
    Module.End R (ExteriorAlgebra R (U →ₗ[R] R)) :=
  Algebra.lmul R (ExteriorAlgebra R (U →ₗ[R] R)) (ι R alpha) *
    contractionOp (evaluationLinear u)

@[simp] theorem singleModeNumberEnd_apply (alpha : U →ₗ[R] R) (u : U)
    (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    singleModeNumberEnd alpha u omega = singleModeNumberOp alpha u omega :=
  rfl

/-- The vacuum has zero occupation. -/
theorem number_op_vacuum_zero (alpha : U →ₗ[R] R) (u : U) :
    singleModeNumberOp alpha u (vacuumState R U) = 0 := by
  unfold singleModeNumberOp
  rw [annihilation_vacuum_zero]
  simp only [creationOp, mul_zero]

/-- Compatibility expansion of the original operator definition. -/
theorem number_op_single_particle_action (alpha beta : U →ₗ[R] R) (u : U) :
    singleModeNumberOp alpha u (singleParticleState beta) =
    creationOp alpha ((contractionOp (evaluationLinear u)) (singleParticleState beta)) :=
  rfl

/-- Actual annihilation of a one-particle state evaluates its covector. -/
theorem annihilation_single_particle (beta : U →ₗ[R] R) (u : U) :
    contractionOp (evaluationLinear u) (singleParticleState beta) =
      beta u • vacuumState R U := by
  rw [single_particle_state_eq_generator, contraction_on_generator]
  simp only [evaluation_linear_apply, vacuumState, Algebra.algebraMap_eq_smul_one]

/-- Actual one-particle action: `N(alpha,u) |beta⟩ = beta(u) |alpha⟩`. -/
theorem number_op_single_particle_evaluation (alpha beta : U →ₗ[R] R) (u : U) :
    singleModeNumberOp alpha u (singleParticleState beta) =
      beta u • singleParticleState alpha := by
  unfold singleModeNumberOp
  rw [annihilation_single_particle]
  change ι R alpha * (beta u • vacuumState R U) =
    beta u • (ι R alpha * vacuumState R U)
  exact mul_smul_comm _ _ _

/-- A normalized occupied one-particle state is fixed by the number operator. -/
theorem number_op_occupied (alpha : U →ₗ[R] R) (u : U) (h : alpha u = 1) :
    singleModeNumberOp alpha u (singleParticleState alpha) =
      singleParticleState alpha := by
  rw [number_op_single_particle_evaluation, h, one_smul]

/-- A one-particle state with zero evaluation has zero occupation in this mode. -/
theorem number_op_unoccupied (alpha beta : U →ₗ[R] R) (u : U) (h : beta u = 0) :
    singleModeNumberOp alpha u (singleParticleState beta) = 0 := by
  rw [number_op_single_particle_evaluation, h, zero_smul]

/-- The occupation quadratic relation holds on every exterior form. -/
theorem number_op_square (alpha : U →ₗ[R] R) (u : U)
    (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    singleModeNumberOp alpha u (singleModeNumberOp alpha u omega) =
      alpha u • singleModeNumberOp alpha u omega := by
  change ι R alpha * contractionOp (evaluationLinear u)
      (ι R alpha * contractionOp (evaluationLinear u) omega) =
    alpha u • (ι R alpha * contractionOp (evaluationLinear u) omega)
  rw [contraction_op_generator_mul, evaluation_linear_apply,
    contraction_op_sq_zero, mul_zero, sub_zero, mul_smul_comm]

/-- A normalized vector-covector pair defines an idempotent occupation map. -/
theorem number_op_idempotent (alpha : U →ₗ[R] R) (u : U) (h : alpha u = 1)
    (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    singleModeNumberOp alpha u (singleModeNumberOp alpha u omega) =
      singleModeNumberOp alpha u omega := by
  rw [number_op_square, h, one_smul]

/-- The same quadratic relation in the actual endomorphism algebra. -/
theorem singleModeNumberEnd_square (alpha : U →ₗ[R] R) (u : U) :
    singleModeNumberEnd alpha u * singleModeNumberEnd alpha u =
      alpha u • singleModeNumberEnd alpha u := by
  apply LinearMap.ext
  intro omega
  exact number_op_square alpha u omega

/-- Normalized occupation is an idempotent endomorphism. -/
theorem singleModeNumberEnd_idempotent (alpha : U →ₗ[R] R) (u : U)
    (h : alpha u = 1) :
    singleModeNumberEnd alpha u * singleModeNumberEnd alpha u =
      singleModeNumberEnd alpha u := by
  rw [singleModeNumberEnd_square, h, one_smul]

/-- A nonzero pairing witnesses a nonzero state on the genuine exterior carrier. -/
theorem single_particle_ne_zero_of_pairing (alpha : U →ₗ[R] R) (u : U)
    (h : alpha u ≠ 0) : singleParticleState alpha ≠ 0 := by
  intro hz
  rw [single_particle_state_eq_generator] at hz
  have halpha : alpha = 0 := (ExteriorAlgebra.ι_eq_zero_iff (R := R) alpha).mp hz
  apply h
  simpa only [LinearMap.zero_apply] using
    congrArg (fun beta : U →ₗ[R] R => beta u) halpha

/-- A normalized mode has a nonzero occupation operator over a nontrivial ring. -/
theorem singleModeNumberEnd_ne_zero [Nontrivial R]
    (alpha : U →ₗ[R] R) (u : U) (h : alpha u = 1) :
    singleModeNumberEnd alpha u ≠ 0 := by
  intro hz
  have hpair : alpha u ≠ 0 := by
    rw [h]
    exact one_ne_zero
  have hstate := single_particle_ne_zero_of_pairing alpha u hpair
  have hfixed : singleModeNumberEnd alpha u (singleParticleState alpha) =
      singleParticleState alpha := number_op_occupied alpha u h
  rw [hz, LinearMap.zero_apply] at hfixed
  exact hstate hfixed.symm

/-- The original compatibility packet retains its statement. -/
theorem master_fock_number_operator_synthesis
    (alpha beta : U →ₗ[R] R) (u : U) :
    (singleModeNumberOp alpha u (vacuumState R U) = 0) ∧
    (singleModeNumberOp alpha u (singleParticleState beta) =
      creationOp alpha ((contractionOp (evaluationLinear u))
        (singleParticleState beta))) :=
  ⟨number_op_vacuum_zero alpha u, rfl⟩

end InfoGeometry.Canonical.FockNumberOperatorBridge
