import InfoGeometry.Topology.SymbolicLatentObservationQuotientNaturality

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# The observational-range functor

For a fixed latent carrier and finite observation index, symbolic-latent
systems form a category under continuous observation-preserving maps.  The
native range map sends such a system to the `TopCat` range of its quotient
observation map.  This owner packages the already-proved identity and
composition laws as an actual `TopCat` functor.
-/

instance symbolicLatentSystemCategory
    {X ι : Type} [TopologicalSpace X] [Fintype ι] :
    Category (FiniteSymbolicLatentSystem X ι) where
  Hom S T := SymbolicLatentMorphism S T
  id S := SymbolicLatentMorphism.id S
  comp := fun {S T U} f g => SymbolicLatentMorphism.comp g f
  id_comp := by
    intro S T F
    cases F
    rfl
  comp_id := by
    intro S T F
    cases F
    rfl
  assoc := by
    intro R S T U h g f
    cases h
    cases g
    cases f
    rfl

def symbolicObservationQuotientRangeFunctor
    {X ι : Type} [TopologicalSpace X] [Fintype ι] :
    (FiniteSymbolicLatentSystem X ι) ⥤ TopCat where
  obj S := TopCat.of (Set.range (symbolicObservationQuotientMap S))
  map F := symbolicObservationQuotientRangeMapOfMorphismTopCatHom F
  map_id S := symbolicObservationQuotientRangeMapOfMorphismTopCatHom_id S
  map_comp f g :=
    symbolicObservationQuotientRangeMapOfMorphismTopCatHom_comp g f

theorem symbolicObservationQuotientRangeFunctor_map_isIso_of_surjective
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun) :
    IsIso ((symbolicObservationQuotientRangeFunctor (X := X) (ι := ι)).map F) := by
  exact symbolicObservationQuotientRangeMapOfMorphismTopCatHom_isIso_of_range_eq
    F (symbolicObservationQuotientRange_eq_of_surjective F hF)

theorem symbolicObservationQuotientRangeFunctor_map_comp
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    symbolicObservationQuotientRangeMapOfMorphismTopCatHom
        (SymbolicLatentMorphism.comp g f) =
      symbolicObservationQuotientRangeMapOfMorphismTopCatHom f ≫
        symbolicObservationQuotientRangeMapOfMorphismTopCatHom g := by
  simpa using symbolicObservationQuotientRangeMapOfMorphismTopCatHom_comp g f

theorem symbolicObservationQuotientRangeFunctor_map_comp_apply
    {X ι : Type}
    [TopologicalSpace X]
    [Fintype ι]
    {S T U : FiniteSymbolicLatentSystem X ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    symbolicObservationQuotientRangeFunctor.map
        (SymbolicLatentMorphism.comp g f) y =
      (symbolicObservationQuotientRangeFunctor.map f ≫
        symbolicObservationQuotientRangeFunctor.map g) y := by
  exact congrArg (fun m => m y)
    (symbolicObservationQuotientRangeFunctor_map_comp
      (X := X) (ι := ι) g f)

end InfoGeometry.Topology
