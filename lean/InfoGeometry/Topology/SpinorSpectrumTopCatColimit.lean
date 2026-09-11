import Mathlib.Topology.Category.TopCat.Limits.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# TopCat colimit template for a two-stage spectral tower

This file packages the smallest honest `TopCat` colimit interface we use in
the topology branch: a two-object tower with a single continuous stage map,
its categorical colimit, the canonical injections, and the universal descent
map. It is intentionally generic so that symbolic-latent or spinor-spectrum
instantiations can reuse it without inventing a parallel colimit theory.
-/

namespace InfoGeometry.Topology.SpinorSpectrumTopCatColimit

open CategoryTheory CategoryTheory.Limits

universe u

inductive SpinorStage where
  | initial
  | extended

inductive SpinorStage.Hom : SpinorStage → SpinorStage → Type
  | idInitial : Hom initial initial
  | step : Hom initial extended
  | idExtended : Hom extended extended

instance : Category SpinorStage where
  Hom := SpinorStage.Hom
  id := fun X =>
    match X with
    | .initial => .idInitial
    | .extended => .idExtended
  comp := by
    intro X Y Z f g
    cases f <;> cases g <;>
      first
        | exact .idInitial
        | exact .step
        | exact .idExtended
  id_comp := by
    intro X Y f
    cases f <;> rfl
  comp_id := by
    intro X Y f
    cases f <;> rfl
  assoc := by
    intro W X Y Z f g h
    cases f <;> cases g <;> cases h <;> rfl

/-- The stage carrier of the two-step spectral tower. -/
def stageCarrier (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1] : SpinorStage → Type u
  | .initial => X0
  | .extended => X1

instance stageTopologicalSpace (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1] (i : SpinorStage) :
    TopologicalSpace (stageCarrier X0 X1 i) := by
  cases i <;> simpa [stageCarrier]

/-- The stage map for the two-step tower. -/
def stageMap (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) : {i j : SpinorStage} → SpinorStage.Hom i j →
      stageCarrier X0 X1 i → stageCarrier X0 X1 j
  | .initial, .initial, .idInitial => id
  | .initial, .extended, .step => f
  | .extended, .extended, .idExtended => id

theorem continuous_stageMap (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f) :
    ∀ {i j} (g : SpinorStage.Hom i j),
      Continuous (stageMap X0 X1 f g)
  | _, _, .idInitial => continuous_id
  | _, _, .step => by
      simpa [stageMap, stageCarrier] using hf
  | _, _, .idExtended => continuous_id

/-- The `TopCat`-valued stage diagram. -/
def spinorSpectrumTopCatDiagram (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f) : SpinorStage ⥤ TopCat where
  obj i := TopCat.of (stageCarrier X0 X1 i)
  map g := TopCat.ofHom
    (ContinuousMap.mk
      (stageMap X0 X1 f g)
      (continuous_stageMap X0 X1 f hf g))
  map_id := by
    intro i
    cases i <;> rfl
  map_comp := by
    intro X Y Z g h
    cases g <;> cases h <;> rfl

/-- The categorical colimit of the two-stage spectral tower. -/
noncomputable def spinorSpectrumTopCatColimit (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f) : TopCat :=
  colimit (spinorSpectrumTopCatDiagram X0 X1 f hf)

/-- The canonical colimit injections. -/
noncomputable def spinorSpectrumTopCatInjection (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f) (i : SpinorStage) :
    (spinorSpectrumTopCatDiagram X0 X1 f hf).obj i ⟶
      spinorSpectrumTopCatColimit X0 X1 f hf :=
  colimit.ι (spinorSpectrumTopCatDiagram X0 X1 f hf) i

theorem spinorSpectrumTopCatInjection_naturality
    {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f)
    {i j : SpinorStage} (g : i ⟶ j) :
    (spinorSpectrumTopCatDiagram X0 X1 f hf).map g ≫
        spinorSpectrumTopCatInjection X0 X1 f hf j =
      spinorSpectrumTopCatInjection X0 X1 f hf i := by
  exact colimit.w (spinorSpectrumTopCatDiagram X0 X1 f hf) g

/-! ## Explicit compatible two-stage readouts -/

def spinorSpectrumTopCatCompatibleCocone
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (spinorSpectrumTopCatDiagram X0 X1 f hf).map SpinorStage.Hom.step ≫ a1 =
        a0) :
    Cocone (spinorSpectrumTopCatDiagram X0 X1 f hf) :=
  { pt := TopCat.of Y
    ι :=
      { app
        | .initial => a0
        | .extended => a1
        naturality := by
            intro i j g
            cases g with
            | idInitial => rfl
            | step => exact hcompat
            | idExtended => rfl } }

noncomputable def spinorSpectrumTopCatCompatibleReadout
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (spinorSpectrumTopCatDiagram X0 X1 f hf).map SpinorStage.Hom.step ≫ a1 =
        a0) :
    spinorSpectrumTopCatColimit X0 X1 f hf ⟶ TopCat.of Y :=
  colimit.desc (spinorSpectrumTopCatDiagram X0 X1 f hf)
    (spinorSpectrumTopCatCompatibleCocone f hf a0 a1 hcompat)

theorem spinorSpectrumTopCatCompatibleReadout_stage
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (spinorSpectrumTopCatDiagram X0 X1 f hf).map SpinorStage.Hom.step ≫ a1 =
        a0)
    (i : SpinorStage) :
    spinorSpectrumTopCatInjection X0 X1 f hf i ≫
        spinorSpectrumTopCatCompatibleReadout f hf a0 a1 hcompat =
      (spinorSpectrumTopCatCompatibleCocone f hf a0 a1 hcompat).ι.app i :=
  by
    exact colimit.ι_desc
      (spinorSpectrumTopCatCompatibleCocone f hf a0 a1 hcompat) i

theorem spinorSpectrumTopCatCompatibleReadout_initial
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (spinorSpectrumTopCatDiagram X0 X1 f hf).map SpinorStage.Hom.step ≫ a1 =
        a0) :
    spinorSpectrumTopCatInjection X0 X1 f hf .initial ≫
        spinorSpectrumTopCatCompatibleReadout f hf a0 a1 hcompat = a0 := by
  simpa [spinorSpectrumTopCatCompatibleCocone] using
    spinorSpectrumTopCatCompatibleReadout_stage f hf a0 a1 hcompat
      SpinorStage.initial

theorem spinorSpectrumTopCatCompatibleReadout_extended
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (spinorSpectrumTopCatDiagram X0 X1 f hf).map SpinorStage.Hom.step ≫ a1 =
        a0) :
    spinorSpectrumTopCatInjection X0 X1 f hf .extended ≫
        spinorSpectrumTopCatCompatibleReadout f hf a0 a1 hcompat = a1 := by
  simpa [spinorSpectrumTopCatCompatibleCocone] using
    spinorSpectrumTopCatCompatibleReadout_stage f hf a0 a1 hcompat
      SpinorStage.extended

end InfoGeometry.Topology.SpinorSpectrumTopCatColimit
