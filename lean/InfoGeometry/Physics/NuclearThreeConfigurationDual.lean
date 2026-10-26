/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfiguration
import InfoGeometry.Physics.NuclearDoubledConfiguration
import InfoGeometry.Clifford.ClNNToDoubledKreinTransport

/-!
# The actual dual and doubled carriers of the three-configuration model

The finite algebraic dual is transported by the existing Riesz equivalence
and the existing neutral-to-doubled realization. The retained projector acts
on both configuration legs. It is independent of the sheet involutions and
does not select a positive sheet. Every scalar and linear map here is real.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfigurationDual

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Clifford.ClNNToDoubledKreinTransport
open InfoGeometry.Physics.NuclearThreeConfiguration
open InfoGeometry.Physics.NuclearDoubledConfiguration

abbrev DualCarrier := PhaseSpaceCarrier ConfigurationSpace
abbrev DoubledCarrier := DoubledSpace ConfigurationSpace

/-- The established finite-rank primal/algebraic-dual realization. -/
def dualRealization : DualCarrier ≃ₗ[ℝ] DoubledCarrier :=
  realizedDoubledRhoEquiv (rieszEquiv 3)

/-- The covector leg transforms by the actual algebraic dual map. -/
def dualAction (A : ConfigurationSpace →L[ℝ] ConfigurationSpace) :
    DualCarrier →ₗ[ℝ] DualCarrier :=
  A.toLinearMap.prodMap A.toLinearMap.dualMap

@[simp] theorem dualAction_apply
    (A : ConfigurationSpace →L[ℝ] ConfigurationSpace) (X : DualCarrier) :
    dualAction A X = (A X.1, X.2.comp A.toLinearMap) := rfl

theorem riesz_symm_dualAction
    (A : ConfigurationSpace →L[ℝ] ConfigurationSpace) (hA : A.adjoint = A)
    (φ : Module.Dual ℝ ConfigurationSpace) :
    (rieszEquiv 3).symm (φ.comp A.toLinearMap) = A ((rieszEquiv 3).symm φ) := by
  apply (rieszEquiv 3).injective
  rw [LinearEquiv.apply_symm_apply]
  ext x
  change φ (A x) = rieszEquiv 3 (A ((rieszEquiv 3).symm φ)) x
  rw [rieszEquiv_apply_apply]
  have hφ : φ (A x) = inner ℝ ((rieszEquiv 3).symm φ) (A x) := by
    rw [← rieszEquiv_apply_apply, LinearEquiv.apply_symm_apply]
  rw [hφ, ← ContinuousLinearMap.adjoint_inner_left, hA]

/-- Self-adjoint configuration maps intertwine the metric-preserving dual
realization with the paired action, including its sum/difference rotation. -/
theorem dualRealization_intertwines
    (A : ConfigurationSpace →L[ℝ] ConfigurationSpace) (hA : A.adjoint = A)
    (X : DualCarrier) :
    dualRealization (dualAction A X) = pairedLift A (dualRealization X) := by
  change realizeToDoubledRho (rieszEquiv 3) (dualAction A X) =
    pairedLift A (realizeToDoubledRho (rieszEquiv 3) X)
  rw [dualAction_apply, realizeToDoubledRho_apply, realizeToDoubledRho_apply]
  simp [riesz_symm_dualAction A hA, map_add, map_sub, map_smul]

theorem dualRealization_pairing (X Y : DualCarrier) :
    canonicalNeutralBilin X Y =
      hessian_indefinite_form (dualRealization X) (dualRealization Y) :=
  canonicalNeutralBilin_realizeToDoubledRho (rieszEquiv 3)
    (rieszEquiv_apply_apply 3) X Y

def dualProjection : DualCarrier →ₗ[ℝ] DualCarrier := dualAction projection
def doubledProjection : DoubledCarrier →L[ℝ] DoubledCarrier := pairedLift projection
def doubledHamiltonian (a c g : ℝ) : DoubledCarrier →L[ℝ] DoubledCarrier :=
  pairedLift (hamiltonian a c g)

theorem dualProjection_idempotent : dualProjection * dualProjection = dualProjection := by
  apply LinearMap.ext
  intro X
  apply Prod.ext
  · exact congrArg (fun A : ConfigurationSpace →L[ℝ] ConfigurationSpace => A X.1)
      projection_idempotent
  · apply LinearMap.ext
    intro x
    change X.2 (projection (projection x)) = X.2 (projection x)
    exact congrArg X.2 (congrArg
      (fun A : ConfigurationSpace →L[ℝ] ConfigurationSpace => A x)
      projection_idempotent)

theorem dualProjection_realization (X : DualCarrier) :
    dualRealization (dualProjection X) = doubledProjection (dualRealization X) :=
  dualRealization_intertwines projection projection_adjoint X

theorem doubledProjection_idempotent :
    doubledProjection * doubledProjection = doubledProjection :=
  pairedLift_idempotent projection projection_idempotent

theorem doubledProjection_kreinAdjoint : kreinAdjoint doubledProjection = doubledProjection := by
  rw [doubledProjection, pairedLift_kreinAdjoint, projection_adjoint]

theorem doubledHamiltonian_kreinAdjoint (a c g : ℝ) :
    kreinAdjoint (doubledHamiltonian a c g) = doubledHamiltonian a c g := by
  rw [doubledHamiltonian, pairedLift_kreinAdjoint, hamiltonian_adjoint]

theorem doubledProjection_preserves_duality :
    doubledProjection.comp (spectral_epsilon (E := ConfigurationSpace)) =
      (spectral_epsilon (E := ConfigurationSpace)).comp doubledProjection ∧
    doubledProjection.comp (modular_j (E := ConfigurationSpace)) =
      (modular_j (E := ConfigurationSpace)).comp doubledProjection ∧
    doubledProjection.comp (clockAxis (E := ConfigurationSpace)) =
      (clockAxis (E := ConfigurationSpace)).comp doubledProjection :=
  ⟨pairedLift_comp_spectral_epsilon projection,
    pairedLift_comp_modular_j projection, pairedLift_comp_clockAxis projection⟩

/-- The retained Krein corner is nondegenerate; null vectors are not ruled out. -/
theorem doubledProjection_nondegenerate (x : DoubledCarrier)
    (hx : doubledProjection x = x)
    (horth : ∀ y : DoubledCarrier, doubledProjection y = y → kreinInner x y = 0) :
    x = 0 :=
  pairedLift_modelCorner_nondegenerate projection projection_idempotent
    projection_adjoint x hx horth

end InfoGeometry.Physics.NuclearThreeConfigurationDual
