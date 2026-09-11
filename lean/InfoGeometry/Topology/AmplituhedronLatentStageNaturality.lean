import InfoGeometry.Topology.AmplituhedronTopCatStageDiagram
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Naturality of the finite amplituhedron latent readout

The coordinate readout is assembled as a natural transformation between the
matrix stage diagram and its coordinate diagram.  The only nontrivial square
is the zero-column inclusion square, proved entrywise.
-/

namespace InfoGeometry.Topology.AmplituhedronColimit

open CategoryTheory CategoryTheory.Limits

def coordinateCarrier : TwoStage → Type
  | .initial => (Fin 4 × Fin 3 → ℝ)
  | .extended => (Fin 4 × Fin 4 → ℝ)

instance coordinateTopologicalSpace (i : TwoStage) :
    TopologicalSpace (coordinateCarrier i) := by
  cases i <;> dsimp [coordinateCarrier] <;> infer_instance

def coordinateMap : {i j : TwoStage} → TwoStage.Hom i j →
    coordinateCarrier i → coordinateCarrier j
  | .initial, .initial, .idInitial => id
  | .initial, .extended, .step => fun f ij =>
      if h : ij.2.val < 3 then f (ij.1, ⟨ij.2.val, h⟩) else 0
  | .extended, .extended, .idExtended => id

theorem continuous_coordinateMap_step :
    Continuous (coordinateMap TwoStage.Hom.step) := by
  unfold coordinateMap
  apply continuous_pi
  intro ij
  by_cases h : ij.2.val < 3
  · simpa [h] using
      (continuous_apply
        (⟨ij.1, (⟨ij.2.val, h⟩ : Fin 3)⟩ : Fin 4 × Fin 3))
  · simpa [h] using
      (continuous_const : Continuous
        (fun _ : (Fin 4 × Fin 3 → ℝ) => (0 : ℝ)))

theorem continuous_coordinateMap : ∀ {i j} (f : TwoStage.Hom i j),
    Continuous (coordinateMap f)
  | _, _, .idInitial => continuous_id
  | _, _, .idExtended => continuous_id
  | _, _, .step => continuous_coordinateMap_step

def coordinateDiagram : TwoStage ⥤ TopCat where
  obj i := TopCat.of (coordinateCarrier i)
  map f := TopCat.ofHom
    (ContinuousMap.mk (coordinateMap f) (continuous_coordinateMap f))
  map_id := by
    intro i
    cases i <;> rfl
  map_comp := by
    intro X Y Z f g
    change TwoStage.Hom X Y at f
    change TwoStage.Hom Y Z at g
    cases f with
    | idInitial => cases g with | idInitial => rfl | step => rfl
    | step => cases g with | idExtended => rfl
    | idExtended => cases g with | idExtended => rfl

def stageReadoutMap : {i : TwoStage} →
    stageCarrier i → coordinateCarrier i
  | .initial => fun M ij => M ij.1 ij.2
  | .extended => fun M ij => M ij.1 ij.2

theorem continuous_stageReadoutMap : ∀ {i},
    Continuous (stageReadoutMap (i := i))
  | .initial => by
      apply continuous_pi
      intro ij
      exact (continuous_apply ij.2).comp (continuous_apply ij.1)
  | .extended => by
      apply continuous_pi
      intro ij
      exact (continuous_apply ij.2).comp (continuous_apply ij.1)

def stageReadout :
    amplituhedronTopCatStageDiagram ⟶ coordinateDiagram where
  app i := TopCat.ofHom
    (ContinuousMap.mk (stageReadoutMap (i := i))
      (continuous_stageReadoutMap (i := i)))
  naturality := by
    intro i j f
    change TwoStage.Hom i j at f
    cases f with
    | idInitial => rfl
    | idExtended => rfl
    | step =>
      ext M
      funext ij
      change (stageReadoutMap (i := .extended)
          (stageMap TwoStage.Hom.step M)) ij =
        (coordinateMap TwoStage.Hom.step
          (stageReadoutMap (i := .initial) M)) ij
      simp only [stageReadoutMap, stageMap, coordinateMap]
      by_cases h : ij.2.val < 3
      · simp [amplituhedronInclusion, h]
      · simp [amplituhedronInclusion, h]

noncomputable def latentStageColimitReadout :
    colimit amplituhedronTopCatStageDiagram ⟶ colimit coordinateDiagram :=
  colim.map stageReadout

theorem latentStageColimitReadout_stage
    (i : TwoStage) :
    amplituhedronTopCatStageInjection i ≫ latentStageColimitReadout =
      stageReadout.app i ≫ colimit.ι coordinateDiagram i := by
  exact colimit.ι_map stageReadout i

theorem latentStageColimitReadout_unique
    (f : colimit amplituhedronTopCatStageDiagram ⟶ colimit coordinateDiagram)
    (h : ∀ i : TwoStage,
      amplituhedronTopCatStageInjection i ≫ f =
        stageReadout.app i ≫ colimit.ι coordinateDiagram i) :
    f = latentStageColimitReadout := by
  apply colimit.hom_ext
  intro i
  exact (h i).trans (latentStageColimitReadout_stage i).symm

end InfoGeometry.Topology.AmplituhedronColimit
