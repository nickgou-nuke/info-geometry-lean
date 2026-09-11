import Mathlib.Topology.Category.TopCat.Limits.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# `TopCat` colimit for a two-stage supergraded Dirac crystal tower

This file owns the categorical `TopCat` colimit interface for a minimal
two-stage tower of topological carriers.  It does not rebuild the algebraic
supercharge relations; those are transported separately by the algebraic
bridge in `WittenOddSquareEvenBridge.lean`.

The only theorem content here is the universal property of the `TopCat`
colimit for this explicit two-object diagram.
-/

namespace InfoGeometry.Physics.SupergradedDiracCrystalTopCatColimit

open CategoryTheory CategoryTheory.Limits

universe u

inductive DiracCrystalStage where
  | initial
  | extended
  deriving DecidableEq

inductive DiracCrystalStage.Hom : DiracCrystalStage → DiracCrystalStage → Type
  | idInitial : Hom initial initial
  | step : Hom initial extended
  | idExtended : Hom extended extended

instance : Category DiracCrystalStage where
  Hom := DiracCrystalStage.Hom
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

/-- The carrier family of the two-stage Dirac crystal tower. -/
def stageCarrier (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1] :
    DiracCrystalStage → Type u
  | .initial => X0
  | .extended => X1

instance stageTopologicalSpace (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1] (i : DiracCrystalStage) :
    TopologicalSpace (stageCarrier X0 X1 i) := by
  cases i <;> simpa [stageCarrier]

/-- The stage map for the two-stage Dirac crystal tower. -/
def stageMap (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) :
    {i j : DiracCrystalStage} → DiracCrystalStage.Hom i j →
      stageCarrier X0 X1 i → stageCarrier X0 X1 j
  | .initial, .initial, .idInitial => id
  | .initial, .extended, .step => f
  | .extended, .extended, .idExtended => id

theorem continuous_stageMap (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f) :
    ∀ {i j} (g : DiracCrystalStage.Hom i j),
      Continuous (stageMap X0 X1 f g)
  | _, _, .idInitial => continuous_id
  | _, _, .step => by
      simpa [stageMap, stageCarrier] using hf
  | _, _, .idExtended => continuous_id

/-- The `TopCat`-valued stage diagram for the Dirac crystal tower. -/
def supergradedDiracCrystalTopCatDiagram (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f) : DiracCrystalStage ⥤ TopCat where
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

/-- The categorical colimit of the Dirac crystal tower. -/
noncomputable def supergradedDiracCrystalTopCatColimit (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f) : TopCat :=
  colimit (supergradedDiracCrystalTopCatDiagram X0 X1 f hf)

/-- The canonical colimit injections. -/
noncomputable def supergradedDiracCrystalTopCatInjection (X0 X1 : Type u)
    [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f) (i : DiracCrystalStage) :
    (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).obj i ⟶
      supergradedDiracCrystalTopCatColimit X0 X1 f hf :=
  colimit.ι (supergradedDiracCrystalTopCatDiagram X0 X1 f hf) i

theorem supergradedDiracCrystalTopCatInjection_naturality
    {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f)
    {i j : DiracCrystalStage} (g : i ⟶ j) :
    (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map g ≫
        supergradedDiracCrystalTopCatInjection X0 X1 f hf j =
      supergradedDiracCrystalTopCatInjection X0 X1 f hf i := by
  exact colimit.w (supergradedDiracCrystalTopCatDiagram X0 X1 f hf) g

/-- The universal descent map from the colimit. -/
noncomputable def supergradedDiracCrystalTopCatDescend
    (X0 X1 : Type u) [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f)
    (c : Cocone (supergradedDiracCrystalTopCatDiagram X0 X1 f hf)) :
    supergradedDiracCrystalTopCatColimit X0 X1 f hf ⟶ c.pt :=
  colimit.desc (supergradedDiracCrystalTopCatDiagram X0 X1 f hf) c

theorem supergradedDiracCrystalTopCatDescend_naturality
    {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f)
    (c : Cocone (supergradedDiracCrystalTopCatDiagram X0 X1 f hf))
    (i : DiracCrystalStage) :
    supergradedDiracCrystalTopCatInjection X0 X1 f hf i ≫
        supergradedDiracCrystalTopCatDescend X0 X1 f hf c =
      c.ι.app i := by
  exact colimit.ι_desc c i

/-- The universal descent map is uniquely determined by the colimit injections. -/
theorem supergradedDiracCrystalTopCatDescend_unique
    {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]
    (f : X0 → X1) (hf : Continuous f)
    (c : Cocone (supergradedDiracCrystalTopCatDiagram X0 X1 f hf))
    {g : supergradedDiracCrystalTopCatColimit X0 X1 f hf ⟶ c.pt}
    (hg : ∀ i : DiracCrystalStage,
      supergradedDiracCrystalTopCatInjection X0 X1 f hf i ≫ g = c.ι.app i) :
    g = supergradedDiracCrystalTopCatDescend X0 X1 f hf c := by
  apply colimit.hom_ext
  intro i
  dsimp [supergradedDiracCrystalTopCatInjection] at hg ⊢
  rw [hg i]
  exact (supergradedDiracCrystalTopCatDescend_naturality f hf c i).symm

/-! ## Explicit compatible two-stage readouts -/

def supergradedDiracCrystalTopCatCompatibleCocone
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map DiracCrystalStage.Hom.step ≫
        a1 = a0) :
    Cocone (supergradedDiracCrystalTopCatDiagram X0 X1 f hf) :=
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

noncomputable def supergradedDiracCrystalTopCatCompatibleReadout
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map DiracCrystalStage.Hom.step ≫
        a1 = a0) :
    supergradedDiracCrystalTopCatColimit X0 X1 f hf ⟶ TopCat.of Y :=
  supergradedDiracCrystalTopCatDescend (X0 := X0) (X1 := X1) f hf
    (supergradedDiracCrystalTopCatCompatibleCocone f hf a0 a1 hcompat)

theorem supergradedDiracCrystalTopCatCompatibleReadout_stage
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map DiracCrystalStage.Hom.step ≫
        a1 = a0)
    (i : DiracCrystalStage) :
    supergradedDiracCrystalTopCatInjection X0 X1 f hf i ≫
        supergradedDiracCrystalTopCatCompatibleReadout f hf a0 a1 hcompat =
      (supergradedDiracCrystalTopCatCompatibleCocone f hf a0 a1 hcompat).ι.app i := by
  simpa [supergradedDiracCrystalTopCatCompatibleReadout] using
    (supergradedDiracCrystalTopCatDescend_naturality f hf
      (supergradedDiracCrystalTopCatCompatibleCocone f hf a0 a1 hcompat) i)

theorem supergradedDiracCrystalTopCatCompatibleReadout_initial
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map DiracCrystalStage.Hom.step ≫
        a1 = a0) :
    supergradedDiracCrystalTopCatInjection X0 X1 f hf .initial ≫
        supergradedDiracCrystalTopCatCompatibleReadout f hf a0 a1 hcompat = a0 := by
  simpa [supergradedDiracCrystalTopCatCompatibleCocone] using
    supergradedDiracCrystalTopCatCompatibleReadout_stage f hf a0 a1 hcompat
      DiracCrystalStage.initial

theorem supergradedDiracCrystalTopCatCompatibleReadout_extended
    {X0 X1 Y : Type u}
    [TopologicalSpace X0] [TopologicalSpace X1] [TopologicalSpace Y]
    (f : X0 → X1) (hf : Continuous f)
    (a0 : TopCat.of X0 ⟶ TopCat.of Y)
    (a1 : TopCat.of X1 ⟶ TopCat.of Y)
    (hcompat :
      (supergradedDiracCrystalTopCatDiagram X0 X1 f hf).map DiracCrystalStage.Hom.step ≫
        a1 = a0) :
    supergradedDiracCrystalTopCatInjection X0 X1 f hf .extended ≫
        supergradedDiracCrystalTopCatCompatibleReadout f hf a0 a1 hcompat = a1 := by
  simpa [supergradedDiracCrystalTopCatCompatibleCocone] using
    supergradedDiracCrystalTopCatCompatibleReadout_stage f hf a0 a1 hcompat
      DiracCrystalStage.extended

end InfoGeometry.Physics.SupergradedDiracCrystalTopCatColimit
