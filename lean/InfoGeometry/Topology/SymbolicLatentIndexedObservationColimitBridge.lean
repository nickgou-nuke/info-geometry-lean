import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentIndexedObservationFunctor

/-!
# Colimit transport for indexed symbolic-latent observations

Indexed coordinate permutations cannot be read into a constant coordinate
object with identity arrows.  The correct target is the coordinate-action
functor, and the induced colimit map is supplied by Mathlib's `colim.map`.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open CategoryTheory.Limits
open TripotentFiveGradeMirrorTopological

noncomputable section

def indexedCoordinateActionTopCatHom
    {ι : Type} [Fintype ι]
    {S T : IndexedSymbolicLatentSystemObject ι}
    (F : IndexedSymbolicLatentSystemHom S T) :
    TopCat.of (ι → ℝ) ⟶ TopCat.of (ι → ℝ) := by
  refine TopCat.ofHom ?_
  let H := indexedCoordinateActionHomeomorph
    (indexedHomeomorphSymm F.indexed)
  exact
    { toFun := indexedCoordinateAction (indexedHomeomorphSymm F.indexed)
      continuous_toFun := H.continuous_toFun }

def indexedCoordinateActionFunctor
    (ι : Type) [Fintype ι] :
    (IndexedSymbolicLatentSystemObject ι) ⥤ TopCat where
  obj _ := TopCat.of (ι → ℝ)
  map F := indexedCoordinateActionTopCatHom F
  map_id S := by
    apply TopCat.hom_ext
    ext v i
    rfl
  map_comp f g := by
    apply TopCat.hom_ext
    ext v i
    change
      v ((f.indexed.index.trans g.indexed.index).symm i) =
        v (f.indexed.index.symm (g.indexed.index.symm i))
    rfl

noncomputable def indexedObservationCoordinateNaturalTransformation
    {J : Type} [Category J]
    {ι : Type} [Fintype ι]
    (D : J ⥤ IndexedSymbolicLatentSystemObject ι) :
    (D ⋙ indexedSymbolicLatentObservationRangeFunctor ι) ⟶
      (D ⋙ indexedCoordinateActionFunctor ι) where
  app j := symbolicObservationQuotientRangeInclusionTopCatHom
    (D.obj j).system
  naturality := by
    intro j k f
    apply TopCat.hom_ext
    ext y i
    rfl

noncomputable def indexedObservationColimitReadout
    {J : Type} [Category J]
    {ι : Type} [Fintype ι]
    (D : J ⥤ IndexedSymbolicLatentSystemObject ι) :
    colimit (D ⋙ indexedSymbolicLatentObservationRangeFunctor ι) ⟶
      colimit (D ⋙ indexedCoordinateActionFunctor ι) :=
  colim.map (indexedObservationCoordinateNaturalTransformation D)

theorem indexedObservationColimitReadout_stage
    {J : Type} [Category J]
    {ι : Type} [Fintype ι]
    (D : J ⥤ IndexedSymbolicLatentSystemObject ι) (j : J) :
    colimit.ι (D ⋙ indexedSymbolicLatentObservationRangeFunctor ι) j ≫
        indexedObservationColimitReadout D =
      (indexedObservationCoordinateNaturalTransformation D).app j ≫
        colimit.ι (D ⋙ indexedCoordinateActionFunctor ι) j :=
  colimit.ι_map (indexedObservationCoordinateNaturalTransformation D) j

theorem indexedObservationColimitReadout_unique
    {J : Type} [Category J]
    {ι : Type} [Fintype ι]
    (D : J ⥤ IndexedSymbolicLatentSystemObject ι)
    (u : colimit (D ⋙ indexedSymbolicLatentObservationRangeFunctor ι) ⟶
      colimit (D ⋙ indexedCoordinateActionFunctor ι))
    (hu : ∀ j,
      colimit.ι (D ⋙ indexedSymbolicLatentObservationRangeFunctor ι) j ≫ u =
        (indexedObservationCoordinateNaturalTransformation D).app j ≫
          colimit.ι (D ⋙ indexedCoordinateActionFunctor ι) j) :
    u = indexedObservationColimitReadout D := by
  apply colimit.hom_ext
  intro j
  rw [hu j, indexedObservationColimitReadout_stage]

end

end InfoGeometry.Topology
