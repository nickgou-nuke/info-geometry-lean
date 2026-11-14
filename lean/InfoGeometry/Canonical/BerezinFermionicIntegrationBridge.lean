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
import InfoGeometry.Canonical.WickTheoremVacuumContractionBridge
import InfoGeometry.Canonical.CrossAnticommutatorBridge
import Mathlib.Tactic.NoncommRing

/-!
# One-mode Berezin operation by native contraction

The operation contracts one selected direction and returns an exterior-algebra
element. For a normalized vector-covector pair it annihilates the vacuum and
sends the selected degree-one state to the unit. Integration over all modes
would require an ordered family of contractions and a top-degree construction;
the statements here concern this one-mode operation.
-/

noncomputable section

namespace InfoGeometry.Canonical.BerezinFermionicIntegrationBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge
open InfoGeometry.Canonical.WickTheoremVacuumContractionBridge
open InfoGeometry.Canonical.CrossAnticommutatorBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- One-mode left Berezin operation, realized by native evaluation contraction. -/
def berezinIntegralOp (u : U) :
    ExteriorAlgebra R (U →ₗ[R] R) →ₗ[R] ExteriorAlgebra R (U →ₗ[R] R) :=
  contractionOp (evaluationLinear u)

/-- The one-mode operation annihilates the unit vacuum. -/
theorem berezin_integral_scalar_zero (u : U) :
    berezinIntegralOp u (vacuumState R U) = 0 :=
  annihilation_vacuum_zero u

/-- Actual one-particle evaluation under the one-mode Berezin operation. -/
theorem berezin_integral_single_particle (u : U) (alpha : U →ₗ[R] R) :
    berezinIntegralOp u (singleParticleState alpha) = alpha u • vacuumState R U := by
  change contractionOp (evaluationLinear u) (singleParticleState alpha) = _
  rw [single_particle_state_eq_generator, contraction_on_generator]
  simp only [evaluation_linear_apply, vacuumState, Algebra.algebraMap_eq_smul_one]

/-- A normalized degree-one state is sent to the actual exterior-algebra unit. -/
theorem berezin_integral_single_particle_one
    (u : U) (alpha : U →ₗ[R] R) (hpair : alpha u = 1) :
    berezinIntegralOp u (singleParticleState alpha) = 1 := by
  simpa only [hpair, one_smul, vacuumState] using
    berezin_integral_single_particle u alpha

/-- Normalization supplies a nonzero operator witness over a nontrivial ring. -/
theorem berezinIntegralOp_ne_zero_of_pairing [Nontrivial R]
    (u : U) (alpha : U →ₗ[R] R) (hpair : alpha u = 1) :
    berezinIntegralOp (R := R) u ≠ 0 := by
  intro hz
  have hunit := berezin_integral_single_particle_one u alpha hpair
  rw [hz, LinearMap.zero_apply] at hunit
  exact zero_ne_one hunit

/-- A concrete real mode integrates its selected generator to one. -/
theorem real_berezin_unit_witness :
    berezinIntegralOp (1 : ℝ)
      (singleParticleState (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) = 1 := by
  exact berezin_integral_single_particle_one (1 : ℝ) LinearMap.id rfl

/-- Compatibility rewriting of the normalized scalar pairing. -/
theorem berezin_integral_generator_one
    (u : U) (alpha : U →ₗ[R] R) (hpair : alpha u = 1) :
    (evaluationLinear u alpha) • (vacuumState R U) =
      (1 : R) • (vacuumState R U) := by
  have h : evaluationLinear u alpha = (1 : R) := by
    rw [evaluation_linear_apply, hpair]
  rw [h]

/-- The original packet records vacuum annihilation and normalized scalar rewriting. -/
theorem master_berezin_fermionic_integration_synthesis
    (u : U) (alpha : U →ₗ[R] R) (hpair : alpha u = 1) :
    ((berezinIntegralOp u (vacuumState R U) = 0) ∧
     ((evaluationLinear u alpha) • (vacuumState R U) =
       (1 : R) • (vacuumState R U))) :=
  ⟨berezin_integral_scalar_zero u, berezin_integral_generator_one u alpha hpair⟩

end InfoGeometry.Canonical.BerezinFermionicIntegrationBridge
