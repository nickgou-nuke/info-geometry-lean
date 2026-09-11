import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopologicalDynamics
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFFiniteMatrixNormedCarrier

/-!
# Finite-stage linear packaging of the compatible-family action

The stage action on readout maps is precomposition by the finite-stage flow.
The current carrier API supports this as a `LinearMap`; a continuous map on
the space of readout maps requires an additional seminormed-space instance.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutStageActionTopCat

open CategoryTheory
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopologicalDynamics

def stageReadoutAction (n : ℕ) (t : ℝ) :
    (InfoGeometry.Clifford.Cl11TensorTower.MatStage n →L[ℝ] ℝ) →ₗ[ℝ]
      (InfoGeometry.Clifford.Cl11TensorTower.MatStage n →L[ℝ] ℝ) := by
  let flow := scalarDilationStageFlow.flow n t
  exact
    { toFun := fun ρ => ρ.comp flow
      map_add' := by
        intro ρ σ
        ext X
        simp
      map_smul' := by
        intro c ρ
        ext X
        simp }

@[simp] theorem stageReadoutAction_apply
    (n : ℕ) (t : ℝ) (ρ : MatStage n →L[ℝ] ℝ) (X : MatStage n) :
    stageReadoutAction n t ρ X =
      ρ ((scalarDilationStageFlow.flow n t) X) := by
  simp [stageReadoutAction]

def stageReadoutActionContinuous (n : ℕ) (t : ℝ) :
    (InfoGeometry.Clifford.Cl11TensorTower.MatStage n →L[ℝ] ℝ) →L[ℝ]
      (InfoGeometry.Clifford.Cl11TensorTower.MatStage n →L[ℝ] ℝ) :=
  (ContinuousLinearMap.flip
      (ContinuousLinearMap.compL ℝ
        (InfoGeometry.Clifford.Cl11TensorTower.MatStage n)
        (InfoGeometry.Clifford.Cl11TensorTower.MatStage n) ℝ))
    (scalarDilationStageFlow.flow n t)

@[simp] theorem stageReadoutActionContinuous_apply
    (n : ℕ) (t : ℝ) (ρ : MatStage n →L[ℝ] ℝ) (X : MatStage n) :
    stageReadoutActionContinuous n t ρ X =
      ρ ((scalarDilationStageFlow.flow n t) X) := by
  rfl

theorem stageReadoutActionContinuous_zero (n : ℕ) :
    stageReadoutActionContinuous n 0 =
      ContinuousLinearMap.id ℝ
        (InfoGeometry.Clifford.Cl11TensorTower.MatStage n →L[ℝ] ℝ) := by
  ext ρ X
  rw [stageReadoutActionContinuous_apply,
    scalarDilationStageFlow.flow_zero]
  rfl

theorem stageReadoutActionContinuous_add
    (n : ℕ) (s t : ℝ) (ρ : MatStage n →L[ℝ] ℝ) (X : MatStage n) :
    stageReadoutActionContinuous n (s + t) ρ X =
      stageReadoutActionContinuous n t
        (stageReadoutActionContinuous n s ρ) X := by
  rw [stageReadoutActionContinuous_apply,
    stageReadoutActionContinuous_apply,
    stageReadoutActionContinuous_apply,
    scalarDilationStageFlow.flow_add]
  rfl

def readoutRestrictionContinuous (n : ℕ) :
    (InfoGeometry.Clifford.Cl11TensorTower.MatStage n →L[ℝ] ℝ) →L[ℝ]
      (InfoGeometry.Clifford.Cl11TensorTower.MatStage (n + 1) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.flip
      (ContinuousLinearMap.compL ℝ
        (InfoGeometry.Clifford.Cl11TensorTower.MatStage (n + 1))
        (InfoGeometry.Clifford.Cl11TensorTower.MatStage n) ℝ))
    (stageRestrictCLM n)

@[simp] theorem readoutRestrictionContinuous_apply
    (n : ℕ) (ρ : MatStage n →L[ℝ] ℝ)
    (X : MatStage (n + 1)) :
    readoutRestrictionContinuous n ρ X = ρ (stageRestrictCLM n X) := by
  rfl

theorem stageReadoutActionContinuous_restriction_naturality
    (n : ℕ) (t : ℝ) (ρ : MatStage n →L[ℝ] ℝ)
    (X : MatStage (n + 1)) :
    readoutRestrictionContinuous n
        (stageReadoutActionContinuous n t ρ) X =
      stageReadoutActionContinuous (n + 1) t
        (readoutRestrictionContinuous n ρ) X := by
  rw [readoutRestrictionContinuous_apply,
    stageReadoutActionContinuous_apply,
    stageReadoutActionContinuous_apply,
    readoutRestrictionContinuous_apply]
  have h := congrArg (fun f => f X)
    (scalarDilationStageFlow.restrict_naturality n t)
  exact congrArg (fun Y => ρ Y) h.symm

def stageReadoutActionTopCatHom (n : ℕ) (t : ℝ) :
    TopCat.of (InfoGeometry.Clifford.Cl11TensorTower.MatStage n →L[ℝ] ℝ) ⟶
      TopCat.of (InfoGeometry.Clifford.Cl11TensorTower.MatStage n →L[ℝ] ℝ) :=
  TopCat.ofHom
    (ContinuousMap.mk (stageReadoutActionContinuous n t)
      (stageReadoutActionContinuous n t).continuous)

theorem coordinateTopCatHom_action_as_stageReadoutAction
    (n : ℕ) (t : ℝ) (ρ : CompatibleContinuousReadoutFamily) :
    (coordinateTopCatHom n)
        (scalarDilationTopCatAction t ρ) =
      stageReadoutAction n t ((coordinateTopCatHom n) ρ) := by
  ext X
  simpa only [stageReadoutAction_apply] using
    coordinateTopCatHom_scalarDilation_naturality t n ρ X

theorem coordinateTopCatHom_action_square
    (n : ℕ) (t : ℝ) :
    scalarDilationTopCatAction t ≫ coordinateTopCatHom n =
      coordinateTopCatHom n ≫ stageReadoutActionTopCatHom n t := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  apply ContinuousLinearMap.ext
  intro X
  simpa only [stageReadoutActionContinuous_apply] using
    coordinateTopCatHom_scalarDilation_naturality t n ρ X

end InfoGeometry.Canonical.RealUHFCompatibleReadoutStageActionTopCat
