import InfoGeometry.Canonical.CubicJordanOsTopologicalReadout
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Filtered `TopCat` diagrams on the native cubic Albert carrier

This file records the genuinely nonconstant part of the topological
construction: transition maps are supplied as data and are required to be
continuous and functorial.  No Jordan product is used or inferred.
-/

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological

variable {J : Type} [Category J]

structure ContinuousAlbertTransitionSystem (J : Type) [Category J] where
  map : ∀ {i j : J}, (i ⟶ j) → AlbertMatrix → AlbertMatrix
  continuous_map : ∀ {i j : J} (f : i ⟶ j), Continuous (map f)
  map_id : ∀ i, map (𝟙 i) = id
  map_comp : ∀ {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (x : AlbertMatrix),
    map g (map f x) = map (f ≫ g) x

def topologicalDiagram (S : ContinuousAlbertTransitionSystem J) :
    J ⥤ TopCat where
  obj _ := TopCat.of AlbertMatrix
  map f := TopCat.ofHom
    { toFun := S.map f
      continuous_toFun := S.continuous_map f }
  map_id := by
    intro i
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change S.map (𝟙 i) x = x
    rw [S.map_id]
    rfl
  map_comp := by
    intro i j k f g
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rw [TopCat.comp_app]
    exact (S.map_comp f g x).symm

noncomputable def topologicalColimit
    (S : ContinuousAlbertTransitionSystem J) : TopCat :=
  colimit (topologicalDiagram S)

noncomputable def topologicalInjection
    (S : ContinuousAlbertTransitionSystem J) (i : J) :
    TopCat.of AlbertMatrix ⟶ topologicalColimit S :=
  colimit.ι (topologicalDiagram S) i

@[reassoc (attr := simp)]
theorem topologicalInjection_transition
    (S : ContinuousAlbertTransitionSystem J)
    {i j : J} (f : i ⟶ j) :
    (topologicalDiagram S).map f ≫ topologicalInjection S j =
      topologicalInjection S i := by
  exact colimit.w (topologicalDiagram S) f

theorem topologicalInjection_transition_apply
    (S : ContinuousAlbertTransitionSystem J)
    {i j : J} (f : i ⟶ j) (x : AlbertMatrix) :
    topologicalInjection S j (S.map f x) = topologicalInjection S i x := by
  exact congrArg (fun g => g x) (topologicalInjection_transition S f)

theorem topologicalInjection_id
    (S : ContinuousAlbertTransitionSystem J) (i : J) :
    topologicalInjection S i ≫ (𝟙 (topologicalColimit S)) =
      topologicalInjection S i := by
  simp

end InfoGeometry.Algebra.CubicJordanOs
