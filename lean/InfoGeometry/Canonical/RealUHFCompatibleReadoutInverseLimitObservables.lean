import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics

/-!
# Observable evaluations on the categorical inverse limit

This owner identifies the concrete evaluation maps on compatible readout
families with the corresponding projections of the native `TopCat` inverse
limit.  It adds no new analytic assumptions: the statement is transported
through the already constructed cone isomorphism.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
open InfoGeometry.Canonical.RealUHFCompatibleReadoutStageActionTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics
open InfoGeometry.Canonical.RealUHFCompatibleStateObservableTopCat

def inverseLimitStageEvaluationTopCatHom
    (n : ℕ) (X : MatStage n) :
    (limit readoutDiagram) ⟶ TopCat.of ℝ :=
  limit.π readoutDiagram n ≫ stageEvaluationTopCatHom n X

theorem stageReadoutActionTopCatHom_evaluation
    (n : ℕ) (t : ℝ) (X : MatStage n) :
    stageReadoutActionTopCatHom n t ≫
        stageEvaluationTopCatHom n X =
      stageEvaluationTopCatHom n
        (scalarDilationStageFlow.flow n t X) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  change stageReadoutActionContinuous n t ρ X =
    ρ (scalarDilationStageFlow.flow n t X)
  rw [stageReadoutActionContinuous_apply]

theorem inverseLimitStageEvaluationTopCatHom_action
    (n : ℕ) (t : ℝ) (X : MatStage n) :
    scalarDilationReadoutInverseLimitAction t ≫
        inverseLimitStageEvaluationTopCatHom n X =
      inverseLimitStageEvaluationTopCatHom n
        (scalarDilationStageFlow.flow n t X) := by
  change scalarDilationReadoutInverseLimitAction t ≫
        (limit.π readoutDiagram n ≫
          stageEvaluationTopCatHom n X) =
      limit.π readoutDiagram n ≫
        stageEvaluationTopCatHom n
          (scalarDilationStageFlow.flow n t X)
  rw [← CategoryTheory.Category.assoc,
    scalarDilationReadoutInverseLimitAction_projection,
    CategoryTheory.Category.assoc]
  change limit.π readoutDiagram n ≫
      stageReadoutActionTopCatHom n t ≫
        stageEvaluationTopCatHom n X =
    limit.π readoutDiagram n ≫
      stageEvaluationTopCatHom n
        (scalarDilationStageFlow.flow n t X)
  rw [stageReadoutActionTopCatHom_evaluation]

theorem inverseLimitStageEvaluation_action_apply
    (ρ : (limit readoutDiagram).carrier)
    (n : ℕ) (t : ℝ) (X : MatStage n) :
    inverseLimitStageEvaluationTopCatHom n X
        (scalarDilationReadoutInverseLimitAction t ρ) =
      inverseLimitStageEvaluationTopCatHom n
        (scalarDilationStageFlow.flow n t X) ρ := by
  have h := congrArg (fun f => f ρ)
    (inverseLimitStageEvaluationTopCatHom_action n t X)
  simpa [TopCat.comp_app] using h

theorem inverseLimitStageEvaluation_action_scalar
    (ρ : (limit readoutDiagram).carrier)
    (n : ℕ) (t : ℝ) (X : MatStage n) :
    inverseLimitStageEvaluationTopCatHom n X
        (scalarDilationReadoutInverseLimitAction t ρ) =
      (Real.exp t) •
        inverseLimitStageEvaluationTopCatHom n X ρ := by
  rw [inverseLimitStageEvaluation_action_apply]
  simp only [scalarDilationStageFlow_apply]
  let f : CompatibleContinuousReadoutFamily :=
    compatibleReadoutInverseLimitIso.inv ρ
  change f.1 n ((Real.exp t) • X) =
    (Real.exp t) • f.1 n X
  exact (f.1 n).map_smul (Real.exp t) X

theorem compatibleReadoutInverseLimitIso_coordinateEvaluation
    (n : ℕ) (X : MatStage n) :
    coordinateEvaluationTopCatHom n X =
      compatibleReadoutInverseLimitIso.hom ≫
        inverseLimitStageEvaluationTopCatHom n X := by
  change coordinateTopCatHom n ≫ stageEvaluationTopCatHom n X =
    compatibleReadoutInverseLimitIso.hom ≫
      (limit.π readoutDiagram n ≫ stageEvaluationTopCatHom n X)
  rw [← Category.assoc]
  rw [show compatibleReadoutInverseLimitIso.hom ≫
        limit.π readoutDiagram n = readoutInverseCone.π.app n by
      simpa [compatibleReadoutInverseLimitIso] using
        (IsLimit.conePointUniqueUpToIso_hom_comp
          readoutInverseConeIsLimit (limit.isLimit readoutDiagram) n)]
  rfl

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables
end
