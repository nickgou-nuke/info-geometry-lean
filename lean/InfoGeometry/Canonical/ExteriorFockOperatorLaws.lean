/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FockNumberOperatorBridge
import InfoGeometry.Canonical.VacuumExpectationCARBridge
import InfoGeometry.Canonical.TwoParticleLiteralOperatorAnnihilationBridge
import InfoGeometry.Canonical.BerezinFermionicIntegrationBridge
import InfoGeometry.Canonical.SplitCliffordUniversalRepresentationBridge
import InfoGeometry.Canonical.FullCARAnticommutationAlgebraBridge

/-!
# Actual exterior Fock and Berezin operator identities

These results evaluate the existing creation and contraction operators. The
mixed CAR and one-particle laws are proved from Mathlib contraction, rather
than being inputs to an abstract annihilation function. They also discharge
the hypotheses of the repository's literal two-particle theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExteriorFockOperatorLaws

open ExteriorAlgebra
open CARSpinorCliffordActionBridge ExteriorContractionOperatorBridge SpinorMixedCARBridge
open FockVacuumAnnihilationBridge SingleParticleFockStateBridge
open MixedCAROperatorAnticommutatorBridge SplitCliffordUniversalRepresentationBridge
open TwoParticleLiteralOperatorAnnihilationBridge BerezinFermionicIntegrationBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

theorem annihilation_creation (u : U) (alpha : Module.Dual R U)
    (omega : ExteriorAlgebra R (Module.Dual R U)) :
    contractionOp (evaluationLinear u) (creationOp alpha omega) =
      alpha u • omega - creationOp alpha (contractionOp (evaluationLinear u) omega) :=
  contraction_op_generator_mul _ _ _

theorem mixedCARAnticommutator_eq (u : U) (alpha : Module.Dual R U)
    (omega : ExteriorAlgebra R (Module.Dual R U)) :
    mixedCARAnticommutator u alpha omega = alpha u • omega :=
  contraction_op_mixed_car _ _ _

theorem annihilation_single_particle (u : U) (alpha : Module.Dual R U) :
    contractionOp (evaluationLinear u) (singleParticleState alpha) =
      alpha u • vacuumState R U := by
  rw [single_particle_state_eq_generator, contraction_op_generator]
  exact Algebra.algebraMap_eq_smul_one (evaluationLinear u alpha)

/-- The existing conditional two-particle theorem now has its native instance. -/
theorem annihilation_two_particle (u : U) (alpha beta : Module.Dual R U) :
    contractionOp (evaluationLinear (R := R) u) (twoParticleState alpha beta) =
      alpha u • singleParticleState beta - beta u • singleParticleState alpha :=
  annihilation_two_particle_operator_pairing (R := R) (U := U) u alpha beta
    (contractionOp (evaluationLinear (R := R) u))
    (annihilation_creation (R := R) (U := U) u)
    (annihilation_single_particle (R := R) (U := U) u beta)

theorem berezin_integral_single_particle (u : U) (alpha : Module.Dual R U) :
    berezinIntegralOp u (singleParticleState alpha) = alpha u • vacuumState R U :=
  annihilation_single_particle u alpha

theorem berezin_integral_normalized (u : U) (alpha : Module.Dual R U)
    (h : alpha u = 1) :
    berezinIntegralOp u (singleParticleState alpha) = vacuumState R U := by
  rw [berezin_integral_single_particle, h, one_smul]

/-- Clifford square on the actual exterior module over any commutative ring. -/
theorem splitCliffordOp_square (u : U) (alpha : Module.Dual R U)
    (omega : ExteriorAlgebra R (Module.Dual R U)) :
    splitCliffordOp u alpha (splitCliffordOp u alpha omega) = alpha u • omega := by
  change contractionOp (evaluationLinear u)
      (contractionOp (evaluationLinear u) omega + creationOp alpha omega) +
    creationOp alpha
      (contractionOp (evaluationLinear u) omega + creationOp alpha omega) = _
  rw [map_add, contraction_op_sq_zero, zero_add]
  have hc : creationOp alpha
      (contractionOp (evaluationLinear u) omega + creationOp alpha omega) =
      creationOp alpha (contractionOp (evaluationLinear u) omega) := by
    simp only [creationOp, mul_add]
    exact add_eq_left.mpr (creation_sq_zero alpha omega)
  rw [hc]
  exact contraction_op_mixed_car _ _ _

end InfoGeometry.Canonical.ExteriorFockOperatorLaws
