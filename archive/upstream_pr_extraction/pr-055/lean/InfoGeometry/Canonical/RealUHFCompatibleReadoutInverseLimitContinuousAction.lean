import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables

/-!
# Continuous-time laws for the inverse-limit readout action

The finite-stage pullback laws are lifted to the native categorical inverse
limit by comparing all morphisms after the limit projections.  This owner
proves only the algebraic action laws; it does not assert a completed UHF
automorphism or a KMS statement.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopological
open InfoGeometry.Canonical.RealUHFCompatibleReadoutStageActionTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
open InfoGeometry.Canonical.RealUHFCompatibleStateObservableTopCat

theorem continuous_coordinateEvaluation_time
    (ρ : CompatibleContinuousReadoutFamily)
    (n : ℕ) (X : MatStage n) :
    Continuous (fun t : ℝ =>
      coordinateEvaluationTopCatHom n X
        (scalarDilationTopCatAction t ρ)) := by
  simpa only [coordinateEvaluationTopCatHom_apply,
    scalarDilationTopCatAction_apply,
    pullback_apply] using
    (continuous_scalarDilation_time_coordinate ρ n X)

theorem stageReadoutActionTopCatHom_zero (n : ℕ) :
    stageReadoutActionTopCatHom n 0 =
      𝟙 (TopCat.of (MatStage n →L[ℝ] ℝ)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  change stageReadoutActionContinuous n 0 ρ = ρ
  exact stageReadoutActionContinuous_zero n ▸ rfl

theorem stageReadoutActionTopCatHom_add
    (n : ℕ) (s t : ℝ) :
    stageReadoutActionTopCatHom n (s + t) =
      stageReadoutActionTopCatHom n s ≫
        stageReadoutActionTopCatHom n t := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  apply ContinuousLinearMap.ext
  intro X
  change stageReadoutActionContinuous n (s + t) ρ X =
    stageReadoutActionContinuous n t
      (stageReadoutActionContinuous n s ρ) X
  exact stageReadoutActionContinuous_add n s t ρ X

theorem scalarDilationReadoutInverseLimitAction_zero :
    scalarDilationReadoutInverseLimitAction 0 =
      𝟙 (limit readoutDiagram) := by
  apply (limit.isLimit readoutDiagram).hom_ext
  intro n
  change scalarDilationReadoutInverseLimitAction 0 ≫
      limit.π readoutDiagram n =
    𝟙 (limit readoutDiagram) ≫ limit.π readoutDiagram n
  rw [scalarDilationReadoutInverseLimitAction_projection]
  change limit.π readoutDiagram n ≫
      stageReadoutActionTopCatHom n 0 =
    limit.π readoutDiagram n
  rw [stageReadoutActionTopCatHom_zero]
  exact Category.comp_id _

theorem scalarDilationReadoutInverseLimitAction_add
    (s t : ℝ) :
    scalarDilationReadoutInverseLimitAction (s + t) =
      scalarDilationReadoutInverseLimitAction s ≫
        scalarDilationReadoutInverseLimitAction t := by
  apply (limit.isLimit readoutDiagram).hom_ext
  intro n
  change scalarDilationReadoutInverseLimitAction (s + t) ≫
      limit.π readoutDiagram n =
    (scalarDilationReadoutInverseLimitAction s ≫
      scalarDilationReadoutInverseLimitAction t) ≫
        limit.π readoutDiagram n
  rw [scalarDilationReadoutInverseLimitAction_projection]
  rw [Category.assoc,
    scalarDilationReadoutInverseLimitAction_projection]
  rw [← Category.assoc,
    scalarDilationReadoutInverseLimitAction_projection]
  change limit.π readoutDiagram n ≫
      stageReadoutActionTopCatHom n (s + t) =
    limit.π readoutDiagram n ≫
      stageReadoutActionTopCatHom n s ≫
        stageReadoutActionTopCatHom n t
  rw [stageReadoutActionTopCatHom_add]

theorem scalarDilationReadoutInverseLimitAction_isIso
    (t : ℝ) :
    IsIso (scalarDilationReadoutInverseLimitAction t) := by
  refine IsIso.mk ⟨scalarDilationReadoutInverseLimitAction (-t), ?_, ?_⟩
  · ext x
    have h := congrArg (fun f => f x)
      (scalarDilationReadoutInverseLimitAction_add t (-t))
    simpa [TopCat.comp_app, scalarDilationReadoutInverseLimitAction_zero]
      using h.symm
  · ext x
    have h := congrArg (fun f => f x)
      (scalarDilationReadoutInverseLimitAction_add (-t) t)
    simpa [TopCat.comp_app, scalarDilationReadoutInverseLimitAction_zero]
      using h.symm

theorem continuous_scalarDilationReadoutInverseLimitAction_time_slice
    (t : ℝ) :
    Continuous (fun ρ : (limit readoutDiagram).carrier =>
      scalarDilationReadoutInverseLimitAction t ρ) := by
  let f : (limit readoutDiagram).carrier →
      CompatibleContinuousReadoutFamily := fun ρ =>
    compatibleReadoutInverseLimitIso.inv ρ
  have hf : Continuous (fun ρ : (limit readoutDiagram).carrier =>
      scalarDilationTopCatAction t (f ρ)) := by
    simpa [f, scalarDilationTopCatAction_apply] using
      continuous_scalarDilation_pullback.comp
        ((continuous_const : Continuous (fun _ :
          (limit readoutDiagram).carrier => t)).prodMk
          (compatibleReadoutInverseLimitIso.inv.hom.continuous.comp
            continuous_id))
  have heq : ∀ ρ : (limit readoutDiagram).carrier,
      scalarDilationReadoutInverseLimitAction t ρ =
        compatibleReadoutInverseLimitIso.hom (scalarDilationTopCatAction t
          (f ρ)) := by
    intro ρ
    have h := congrArg (fun g => g (f ρ))
      (scalarDilationReadoutInverseLimitAction_transport t)
    simpa [TopCat.comp_app, f] using h.symm
  rw [show (fun ρ : (limit readoutDiagram).carrier =>
      scalarDilationReadoutInverseLimitAction t ρ) =
      (fun ρ => compatibleReadoutInverseLimitIso.hom
        (scalarDilationTopCatAction t (f ρ))) by
      funext ρ
      exact heq ρ]
  exact compatibleReadoutInverseLimitIso.hom.hom.continuous.comp hf

noncomputable def scalarDilationReadoutInverseLimitActionHomeomorph
    (t : ℝ) :
    (limit readoutDiagram).carrier ≃ₜ
      (limit readoutDiagram).carrier where
  toFun := scalarDilationReadoutInverseLimitAction t
  invFun := scalarDilationReadoutInverseLimitAction (-t)
  left_inv := by
    intro x
    have h := congrArg (fun f => f x)
      (scalarDilationReadoutInverseLimitAction_add t (-t))
    simpa [TopCat.comp_app, scalarDilationReadoutInverseLimitAction_zero]
      using h.symm
  right_inv := by
    intro x
    have h := congrArg (fun f => f x)
      (scalarDilationReadoutInverseLimitAction_add (-t) t)
    simpa [TopCat.comp_app, scalarDilationReadoutInverseLimitAction_zero]
      using h.symm
  continuous_toFun := by
    exact continuous_scalarDilationReadoutInverseLimitAction_time_slice t
  continuous_invFun := by
    exact continuous_scalarDilationReadoutInverseLimitAction_time_slice (-t)

@[simp] theorem scalarDilationReadoutInverseLimitActionHomeomorph_apply
    (t : ℝ) (ρ : (limit readoutDiagram).carrier) :
    scalarDilationReadoutInverseLimitActionHomeomorph t ρ =
      scalarDilationReadoutInverseLimitAction t ρ := rfl

theorem scalarDilationReadoutInverseLimitActionHomeomorph_zero_apply
    (ρ : (limit readoutDiagram).carrier) :
    scalarDilationReadoutInverseLimitActionHomeomorph 0 ρ = ρ := by
  change scalarDilationReadoutInverseLimitAction 0 ρ = ρ
  have h := congrArg (fun f => f ρ)
    scalarDilationReadoutInverseLimitAction_zero
  simpa using h

theorem scalarDilationReadoutInverseLimitActionHomeomorph_add_apply
    (s t : ℝ) (ρ : (limit readoutDiagram).carrier) :
    scalarDilationReadoutInverseLimitActionHomeomorph (s + t) ρ =
      scalarDilationReadoutInverseLimitActionHomeomorph t
        (scalarDilationReadoutInverseLimitActionHomeomorph s ρ) := by
  change scalarDilationReadoutInverseLimitAction (s + t) ρ =
    scalarDilationReadoutInverseLimitAction t
      (scalarDilationReadoutInverseLimitAction s ρ)
  have h := congrArg (fun f => f ρ)
    (scalarDilationReadoutInverseLimitAction_add s t)
  simpa [TopCat.comp_app] using h

theorem scalarDilationReadoutInverseLimitAction_transport_inv
    (t : ℝ) :
    scalarDilationReadoutInverseLimitAction t ≫
        compatibleReadoutInverseLimitIso.inv =
      compatibleReadoutInverseLimitIso.inv ≫
        scalarDilationTopCatAction t := by
  apply (cancel_mono compatibleReadoutInverseLimitIso.hom).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]
  rw [scalarDilationReadoutInverseLimitAction_transport]
  simp

theorem continuous_scalarDilationReadoutInverseLimitAction_orbit
    (ρ : (limit readoutDiagram).carrier) :
    Continuous (fun t : ℝ =>
      scalarDilationReadoutInverseLimitAction t ρ) := by
  let ρ' : CompatibleContinuousReadoutFamily :=
    compatibleReadoutInverseLimitIso.inv ρ
  have hfamily : Continuous (fun t : ℝ =>
      scalarDilationTopCatAction t ρ') := by
    simpa [scalarDilationTopCatAction_apply] using
      continuous_scalarDilation_pullback.comp
        ((continuous_id : Continuous (fun t : ℝ => t)).prodMk
          (continuous_const : Continuous (fun _ : ℝ => ρ')))
  have htransport : ∀ t : ℝ,
      scalarDilationReadoutInverseLimitAction t ρ =
        compatibleReadoutInverseLimitIso.hom
          (scalarDilationTopCatAction t ρ') := by
    intro t
    have h := congrArg
      (fun f => f ρ)
      (scalarDilationReadoutInverseLimitAction_transport_inv t)
    have h' := congrArg
      (fun x => compatibleReadoutInverseLimitIso.hom x) h
    simpa [TopCat.comp_app, ρ'] using h'
  rw [show (fun t : ℝ =>
      scalarDilationReadoutInverseLimitAction t ρ) =
      (fun t : ℝ => compatibleReadoutInverseLimitIso.hom
        (scalarDilationTopCatAction t ρ')) by
      funext t
      exact htransport t]
  exact compatibleReadoutInverseLimitIso.hom.hom.continuous.comp hfamily

theorem continuous_scalarDilationReadoutInverseLimitAction_joint :
    Continuous (fun p : ℝ × (limit readoutDiagram).carrier =>
      scalarDilationReadoutInverseLimitAction p.1 p.2) := by
  let f : ℝ × (limit readoutDiagram).carrier →
      ℝ × CompatibleContinuousReadoutFamily := fun p =>
    (p.1, compatibleReadoutInverseLimitIso.inv p.2)
  have hf : Continuous f := by
    apply continuous_fst.prodMk
    exact compatibleReadoutInverseLimitIso.inv.hom.continuous.comp
      continuous_snd
  have hbase : Continuous (fun p : ℝ × (limit readoutDiagram).carrier =>
      scalarDilationTopCatAction p.1
        (compatibleReadoutInverseLimitIso.inv p.2)) := by
    simpa [f, scalarDilationTopCatAction_apply] using
      continuous_scalarDilation_pullback.comp hf
  have htransport : ∀ p : ℝ × (limit readoutDiagram).carrier,
      scalarDilationReadoutInverseLimitAction p.1 p.2 =
        compatibleReadoutInverseLimitIso.hom
          (scalarDilationTopCatAction p.1
            (compatibleReadoutInverseLimitIso.inv p.2)) := by
    intro p
    have h := congrArg
      (fun g => g p.2)
      (scalarDilationReadoutInverseLimitAction_transport_inv p.1)
    have h' := congrArg
      (fun x => compatibleReadoutInverseLimitIso.hom x) h
    simpa [TopCat.comp_app] using h'
  rw [show (fun p : ℝ × (limit readoutDiagram).carrier =>
      scalarDilationReadoutInverseLimitAction p.1 p.2) =
      (fun p : ℝ × (limit readoutDiagram).carrier =>
        compatibleReadoutInverseLimitIso.hom
          (scalarDilationTopCatAction p.1
            (compatibleReadoutInverseLimitIso.inv p.2))) by
      funext p
      exact htransport p]
  exact compatibleReadoutInverseLimitIso.hom.hom.continuous.comp hbase

noncomputable def scalarDilationReadoutInverseLimitActionJointTopCatHom :
    TopCat.of (ℝ × (limit readoutDiagram).carrier) ⟶
      TopCat.of (limit readoutDiagram).carrier :=
  TopCat.ofHom
    { toFun := fun p =>
        scalarDilationReadoutInverseLimitAction p.1 p.2
      continuous_toFun :=
        continuous_scalarDilationReadoutInverseLimitAction_joint }

@[simp] theorem scalarDilationReadoutInverseLimitActionJointTopCatHom_apply
    (p : ℝ × (limit readoutDiagram).carrier) :
    scalarDilationReadoutInverseLimitActionJointTopCatHom p =
      scalarDilationReadoutInverseLimitAction p.1 p.2 := rfl

theorem continuous_inverseLimitStageEvaluation_joint
    (n : ℕ) (X : MatStage n) :
    Continuous (fun p : ℝ × (limit readoutDiagram).carrier =>
      inverseLimitStageEvaluationTopCatHom n X
        (scalarDilationReadoutInverseLimitAction p.1 p.2)) := by
  exact (inverseLimitStageEvaluationTopCatHom n X).hom.continuous.comp
    continuous_scalarDilationReadoutInverseLimitAction_joint

theorem continuous_inverseLimitStageEvaluation_time
    (ρ : (limit readoutDiagram).carrier)
    (n : ℕ) (X : MatStage n) :
    Continuous (fun t : ℝ =>
      inverseLimitStageEvaluationTopCatHom n X
        (scalarDilationReadoutInverseLimitAction t ρ)) := by
  let ρ' : CompatibleContinuousReadoutFamily :=
    compatibleReadoutInverseLimitIso.inv ρ
  have hρ' : Continuous (fun t : ℝ =>
      coordinateEvaluationTopCatHom n X
        (scalarDilationTopCatAction t ρ')) :=
    continuous_coordinateEvaluation_time ρ' n X
  have hInv :
      compatibleReadoutInverseLimitIso.inv ≫
          coordinateEvaluationTopCatHom n X =
        inverseLimitStageEvaluationTopCatHom n X := by
    rw [compatibleReadoutInverseLimitIso_coordinateEvaluation]
    simp
  have hEq :
      (fun t : ℝ =>
        inverseLimitStageEvaluationTopCatHom n X
          (scalarDilationReadoutInverseLimitAction t ρ)) =
      (fun t : ℝ =>
        coordinateEvaluationTopCatHom n X
          (scalarDilationTopCatAction t ρ')) := by
    funext t
    have h₁ := congrArg
      (fun f => f (scalarDilationReadoutInverseLimitAction t ρ))
      hInv.symm
    have h₂ := congrArg (fun f => f ρ)
      (scalarDilationReadoutInverseLimitAction_transport_inv t)
    change inverseLimitStageEvaluationTopCatHom n X
        (scalarDilationReadoutInverseLimitAction t ρ) =
      coordinateEvaluationTopCatHom n X
        (compatibleReadoutInverseLimitIso.inv
          (scalarDilationReadoutInverseLimitAction t ρ)) at h₁
    change compatibleReadoutInverseLimitIso.inv
        (scalarDilationReadoutInverseLimitAction t ρ) =
      scalarDilationTopCatAction t
        (compatibleReadoutInverseLimitIso.inv ρ) at h₂
    rw [h₁, h₂]
  rw [hEq]
  exact hρ'

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction

end
