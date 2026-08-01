import InfoGeometry.Canonical.CubicJordanOsFilteredTopCat

/-!
# Continuous cocones and descent for filtered Albert stages

The transition-system owner supplies the diagram.  This file supplies its
universal cocone interface: any continuous compatible family of Albert-stage
readouts descends uniquely to the categorical `TopCat` colimit.
-/

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological

variable {J : Type} [Category J]

structure ContinuousAlbertCocone
    (S : ContinuousAlbertTransitionSystem J)
    (Y : Type) [TopologicalSpace Y] where
  ι : J → AlbertMatrix → Y
  continuous_ι : ∀ i, Continuous (ι i)
  ι_comm : ∀ {i j : J} (f : i ⟶ j) (x : AlbertMatrix),
    ι j (S.map f x) = ι i x

def ιTopCatHom
    {S : ContinuousAlbertTransitionSystem J}
    {Y : Type} [TopologicalSpace Y]
    (C : ContinuousAlbertCocone S Y) (i : J) :
    TopCat.of AlbertMatrix ⟶ TopCat.of Y :=
  TopCat.ofHom
    { toFun := C.ι i
      continuous_toFun := C.continuous_ι i }

def toTopCatCocone
    {S : ContinuousAlbertTransitionSystem J}
    {Y : Type} [TopologicalSpace Y]
    (C : ContinuousAlbertCocone S Y) :
    Cocone (topologicalDiagram S) where
  pt := TopCat.of Y
  ι :=
    { app := fun i => ιTopCatHom C i
      naturality := by
        intro i j f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        rw [TopCat.comp_app]
        exact C.ι_comm f x }

noncomputable def coconeDescend
    {S : ContinuousAlbertTransitionSystem J}
    {Y : Type} [TopologicalSpace Y]
    (C : ContinuousAlbertCocone S Y) :
    topologicalColimit S ⟶ TopCat.of Y :=
  topologicalDirectDescend (topologicalDiagram S) (toTopCatCocone C)

theorem coconeDescend_stage
    {S : ContinuousAlbertTransitionSystem J}
    {Y : Type} [TopologicalSpace Y]
    (C : ContinuousAlbertCocone S Y) (i : J) :
    topologicalInjection S i ≫ coconeDescend C = ιTopCatHom C i := by
  exact topologicalDirectDescend_stage (topologicalDiagram S)
    (toTopCatCocone C) i

theorem coconeDescend_stage_apply
    {S : ContinuousAlbertTransitionSystem J}
    {Y : Type} [TopologicalSpace Y]
    (C : ContinuousAlbertCocone S Y) (i : J) (x : AlbertMatrix) :
    coconeDescend C (topologicalInjection S i x) = C.ι i x := by
  exact congrArg (fun g => g x) (coconeDescend_stage C i)

theorem coconeDescend_unique
    {S : ContinuousAlbertTransitionSystem J}
    {Y : Type} [TopologicalSpace Y]
    (C : ContinuousAlbertCocone S Y)
    (f : topologicalColimit S ⟶ TopCat.of Y)
    (hf : ∀ i : J, topologicalInjection S i ≫ f = ιTopCatHom C i) :
    f = coconeDescend C := by
  apply topologicalDirectDescend_unique (topologicalDiagram S)
    (toTopCatCocone C) f
  intro i
  exact hf i

end InfoGeometry.Algebra.CubicJordanOs
