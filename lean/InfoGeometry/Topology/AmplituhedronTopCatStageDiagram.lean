import Mathlib.Topology.Category.TopCat.Limits.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.AmplituhedronTensorTowerColimit

/-!
# A native finite stage diagram in `TopCat`

The two objects are the three- and four-column matrix stages.  The unique
non-identity arrow is the existing zero-column inclusion.  This file exposes
the actual functor and its categorical colimit; it does not identify that
finite colimit with an infinite amplituhedron or with scattering data.
-/

namespace InfoGeometry.Topology.AmplituhedronColimit

open CategoryTheory CategoryTheory.Limits

inductive TwoStage where
  | initial
  | extended

inductive TwoStage.Hom : TwoStage → TwoStage → Type
  | idInitial : Hom initial initial
  | step : Hom initial extended
  | idExtended : Hom extended extended

instance : Category TwoStage where
  Hom := TwoStage.Hom
  id := fun X => match X with
    | .initial => .idInitial
    | .extended => .idExtended
  comp := by
    intro X Y Z f g
    cases f <;> cases g <;>
      first | exact .idInitial | exact .step | exact .idExtended
  id_comp := by
    intro X Y f
    cases f <;> rfl
  comp_id := by
    intro X Y f
    cases f <;> rfl
  assoc := by
    intro W X Y Z f g h
    cases f <;> cases g <;> cases h <;> rfl

def stageCarrier : TwoStage → Type
  | .initial => AmplituhedronAlgebra 3
  | .extended => AmplituhedronAlgebra 4

instance stageTopologicalSpace (i : TwoStage) :
    TopologicalSpace (stageCarrier i) := by
  cases i <;> dsimp [stageCarrier] <;> infer_instance

def stageMap : {i j : TwoStage} → TwoStage.Hom i j →
    stageCarrier i → stageCarrier j
  | .initial, .initial, .idInitial => id
  | .initial, .extended, .step => amplituhedronInclusion 3
  | .extended, .extended, .idExtended => id

theorem continuous_stageMap : ∀ {i j} (f : TwoStage.Hom i j),
    Continuous (stageMap f)
  | _, _, .idInitial => continuous_id
  | _, _, .step => by
      unfold stageMap amplituhedronInclusion
      fun_prop
  | _, _, .idExtended => continuous_id

def amplituhedronTopCatStageDiagram : TwoStage ⥤ TopCat where
  obj i := TopCat.of (stageCarrier i)
  map f := TopCat.ofHom
    (ContinuousMap.mk (stageMap f) (continuous_stageMap f))
  map_id := by
    intro i
    cases i <;> rfl
  map_comp := by
    intro X Y Z f g
    change TwoStage.Hom X Y at f
    change TwoStage.Hom Y Z at g
    cases f with
    | idInitial =>
      cases g with
      | idInitial => rfl
      | step => rfl
    | step =>
      cases g with
      | idExtended => rfl
    | idExtended =>
      cases g with
      | idExtended => rfl

noncomputable def amplituhedronTopCatStageColimit : TopCat :=
  colimit amplituhedronTopCatStageDiagram

noncomputable def amplituhedronTopCatStageInjection (i : TwoStage) :
    amplituhedronTopCatStageDiagram.obj i ⟶
      amplituhedronTopCatStageColimit :=
  colimit.ι amplituhedronTopCatStageDiagram i

theorem amplituhedronTopCatStageInjection_naturality
    {i j : TwoStage} (f : i ⟶ j) :
    amplituhedronTopCatStageDiagram.map f ≫
        amplituhedronTopCatStageInjection j =
      amplituhedronTopCatStageInjection i := by
  exact colimit.w amplituhedronTopCatStageDiagram f

noncomputable def amplituhedronTopCatStageDescend
    (c : Cocone amplituhedronTopCatStageDiagram) :
    amplituhedronTopCatStageColimit ⟶ c.pt :=
  colimit.desc amplituhedronTopCatStageDiagram c

theorem amplituhedronTopCatStageDescend_naturality
    (c : Cocone amplituhedronTopCatStageDiagram) (i : TwoStage) :
    amplituhedronTopCatStageInjection i ≫
        amplituhedronTopCatStageDescend c = c.ι.app i := by
  exact colimit.ι_desc c i

end InfoGeometry.Topology.AmplituhedronColimit
