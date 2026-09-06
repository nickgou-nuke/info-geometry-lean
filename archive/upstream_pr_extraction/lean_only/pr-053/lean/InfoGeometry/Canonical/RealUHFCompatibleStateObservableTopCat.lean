import InfoGeometry.Canonical.RealUHFCompatibleReadoutStageAction

/-!
# Continuous finite-stage observables on compatible readout families

Evaluation at a fixed finite-stage matrix is a continuous TopCat morphism.
This gives a small observable layer over the projective compatible-family
carrier and records its covariance under the scalar stage action.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateObservableTopCat

open CategoryTheory
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopologicalDynamics

def stageEvaluationCLM (n : ℕ) (X : MatStage n) :
    (MatStage n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ) X

def stageEvaluationTopCatHom (n : ℕ) (X : MatStage n) :
    TopCat.of (MatStage n →L[ℝ] ℝ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    (ContinuousMap.mk (stageEvaluationCLM n X)
      (stageEvaluationCLM n X).continuous)

@[simp] theorem stageEvaluationTopCatHom_apply
    (n : ℕ) (X : MatStage n) (ρ : MatStage n →L[ℝ] ℝ) :
    stageEvaluationTopCatHom n X ρ = ρ X := by
  change stageEvaluationCLM n X ρ = ρ X
  rfl

def coordinateEvaluationTopCatHom (n : ℕ) (X : MatStage n) :
    TopCat.of CompatibleContinuousReadoutFamily ⟶ TopCat.of ℝ :=
  coordinateTopCatHom n ≫ stageEvaluationTopCatHom n X

@[simp] theorem coordinateEvaluationTopCatHom_apply
    (n : ℕ) (X : MatStage n)
    (ρ : CompatibleContinuousReadoutFamily) :
    coordinateEvaluationTopCatHom n X ρ = ρ.1 n X := by
  change stageEvaluationCLM n X ((coordinateTopCatHom n) ρ) = ρ.1 n X
  change ((coordinateTopCatHom n) ρ) X = ρ.1 n X
  rfl

theorem coordinateEvaluationTopCatHom_action
    (t : ℝ) (n : ℕ) (X : MatStage n)
    (ρ : CompatibleContinuousReadoutFamily) :
    coordinateEvaluationTopCatHom n X
        (scalarDilationTopCatAction t ρ) =
      coordinateEvaluationTopCatHom n
        ((scalarDilationStageFlow.flow n t) X) ρ := by
  simpa only [coordinateEvaluationTopCatHom_apply] using
    coordinateTopCatHom_scalarDilation_naturality t n ρ X

theorem coordinateEvaluationTopCatHom_restriction
    (n : ℕ) (X : MatStage (n + 1))
    (ρ : CompatibleContinuousReadoutFamily) :
    coordinateEvaluationTopCatHom n (stageRestrictCLM n X) ρ =
      coordinateEvaluationTopCatHom (n + 1) X ρ := by
  rw [coordinateEvaluationTopCatHom_apply,
    coordinateEvaluationTopCatHom_apply]
  have h := congrArg (fun f => f X) (ρ.2 n)
  exact h

theorem coordinateEvaluationTopCatHom_restriction_naturality
    (n : ℕ) (X : MatStage (n + 1)) :
    coordinateEvaluationTopCatHom n (stageRestrictCLM n X) =
      coordinateEvaluationTopCatHom (n + 1) X := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  exact coordinateEvaluationTopCatHom_restriction n X ρ

end InfoGeometry.Canonical.RealUHFCompatibleStateObservableTopCat
