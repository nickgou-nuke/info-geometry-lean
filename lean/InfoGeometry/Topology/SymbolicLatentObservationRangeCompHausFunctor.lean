import InfoGeometry.Topology.SymbolicLatentObservationRangeCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationQuotientNaturality
import InfoGeometry.Topology.SymbolicLatentObservationRangeFunctor

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

/-- The compact Hausdorff map on observation ranges induced by a native
symbolic-latent system morphism.  Both source and target are compact ranges;
the ambient feature space is deliberately not treated as compact. -/
noncomputable def symbolicObservationRangeCompHausHomOfMorphism
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T) :
    symbolicObservationRangeCompHaus S ⟶ symbolicObservationRangeCompHaus T := by
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp (isCompact_symbolicObservationQuotient_range S)
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap T)) :=
    isCompact_iff_compactSpace.mp (isCompact_symbolicObservationQuotient_range T)
  dsimp [symbolicObservationRangeCompHaus]
  change CompHaus.of (Set.range (symbolicObservationQuotientMap S)) ⟶
    CompHaus.of (Set.range (symbolicObservationQuotientMap T))
  exact ⟨TopCat.ofHom
    { toFun := symbolicObservationQuotientRangeMapOfMorphism F
      continuous_toFun := continuous_symbolicObservationQuotientRangeMapOfMorphism F }⟩

/-- Forgetting compact-Hausdorff structure recovers the native `TopCat` map. -/
theorem symbolicObservationRangeCompHausHomOfMorphism_forget
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T) :
    compHausToTop.map (symbolicObservationRangeCompHausHomOfMorphism F) =
      symbolicObservationQuotientRangeMapOfMorphismTopCatHom F := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

theorem symbolicObservationRangeCompHausHomOfMorphism_id
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicObservationRangeCompHausHomOfMorphism
        (SymbolicLatentMorphism.id S) =
      𝟙 (symbolicObservationRangeCompHaus S) := by
  apply ConcreteCategory.hom_ext
  intro y
  rfl

theorem symbolicObservationRangeCompHausHomOfMorphism_comp
    {S T U : FiniteSymbolicLatentSystem X ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    symbolicObservationRangeCompHausHomOfMorphism
        (SymbolicLatentMorphism.comp g f) =
      symbolicObservationRangeCompHausHomOfMorphism f ≫
        symbolicObservationRangeCompHausHomOfMorphism g := by
  apply ConcreteCategory.hom_ext
  intro y
  rfl

theorem symbolicObservationRangeCompHausHomOfMorphism_isIso_of_surjective
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun) :
    IsIso (symbolicObservationRangeCompHausHomOfMorphism F) := by
  have hIso :
      IsIso (symbolicObservationQuotientRangeMapOfMorphismTopCatHom F) :=
    symbolicObservationQuotientRangeMapOfMorphismTopCatHom_isIso_of_surjective F hF
  haveI : IsIso (compHausToTop.map (symbolicObservationRangeCompHausHomOfMorphism F)) := by
    simpa [symbolicObservationRangeCompHausHomOfMorphism_forget] using hIso
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  exact hFF.isIso_of_isIso_map (symbolicObservationRangeCompHausHomOfMorphism F)

/-- The native observation-range functor also exists in `CompHaus`: its
objects are compact Hausdorff ranges and its arrows are the induced range
maps. -/
noncomputable def symbolicLatentObservationRangeCompHausFunctor :
    (FiniteSymbolicLatentSystem X ι) ⥤ CompHaus where
  obj S := symbolicObservationRangeCompHaus S
  map F := symbolicObservationRangeCompHausHomOfMorphism F
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro y
    change symbolicObservationQuotientRangeMapOfMorphism (𝟙 S) y = y
    exact congrFun (symbolicObservationQuotientRangeMapOfMorphism_id S) y
  map_comp f g := by
    exact symbolicObservationRangeCompHausHomOfMorphism_comp g f

theorem symbolicLatentObservationRangeCompHausFunctor_map_id
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicLatentObservationRangeCompHausFunctor.map
        (SymbolicLatentMorphism.id S) =
      𝟙 (symbolicObservationRangeCompHaus S) := by
  simpa using symbolicObservationRangeCompHausHomOfMorphism_id
    (X := X) (ι := ι) S

theorem symbolicLatentObservationRangeCompHausFunctor_map_comp
    {S T U : FiniteSymbolicLatentSystem X ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    symbolicLatentObservationRangeCompHausFunctor.map
        (SymbolicLatentMorphism.comp g f) =
      symbolicLatentObservationRangeCompHausFunctor.map f ≫
        symbolicLatentObservationRangeCompHausFunctor.map g := by
  simpa using symbolicObservationRangeCompHausHomOfMorphism_comp g f

theorem symbolicLatentObservationRangeCompHausFunctor_map_comp_apply
    {S T U : FiniteSymbolicLatentSystem X ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (x : symbolicObservationRangeCompHaus S) :
    symbolicLatentObservationRangeCompHausFunctor.map
        (SymbolicLatentMorphism.comp g f) x =
      (symbolicLatentObservationRangeCompHausFunctor.map f ≫
        symbolicLatentObservationRangeCompHausFunctor.map g) x := by
  exact congrArg (fun m => m x)
    (symbolicLatentObservationRangeCompHausFunctor_map_comp
      (X := X) (ι := ι) g f)

theorem symbolicLatentObservationRangeCompHausFunctor_map_isIso_of_surjective
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun) :
    IsIso (symbolicLatentObservationRangeCompHausFunctor.map F) := by
  simpa using symbolicObservationRangeCompHausHomOfMorphism_isIso_of_surjective
    (X := X) (ι := ι) F hF

/-- A surjective morphism induces a canonical isomorphism of compact
Hausdorff observation ranges. -/
noncomputable def symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun) :
    symbolicObservationRangeCompHaus S ≅ symbolicObservationRangeCompHaus T := by
  letI : IsIso (symbolicObservationRangeCompHausHomOfMorphism F) :=
    symbolicObservationRangeCompHausHomOfMorphism_isIso_of_surjective
      (X := X) (ι := ι) F hF
  exact asIso (symbolicObservationRangeCompHausHomOfMorphism F)

@[simp] theorem symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective_hom_apply
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun)
    (x : symbolicObservationRangeCompHaus S) :
    (symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).hom x =
      symbolicObservationRangeCompHausHomOfMorphism F x := by
  rfl

@[simp] theorem symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective_hom_inv_id
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun) :
    (symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).hom ≫
      (symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).inv =
        𝟙 _ := by
  exact (symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
    (X := X) (ι := ι) F hF).hom_inv_id

@[simp] theorem symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective_hom_inv_apply
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun)
    (x : symbolicObservationRangeCompHaus S) :
  (((symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).hom ≫
      (symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).inv) x).1 =
        x.1 := by
  exact congrArg Subtype.val <|
    congrArg (fun f => f x)
      ((symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).hom_inv_id)

@[simp] theorem symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective_inv_hom_id
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun) :
    (symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).inv ≫
      (symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).hom =
        𝟙 _ := by
  exact (symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
    (X := X) (ι := ι) F hF).inv_hom_id

@[simp] theorem symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective_inv_hom_apply
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun)
    (x : symbolicObservationRangeCompHaus T) :
  (((symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).inv ≫
      (symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).hom) x).1 =
        x.1 := by
  exact congrArg Subtype.val <|
    congrArg (fun f => f x)
      ((symbolicLatentObservationRangeCompHausFunctor_mapIso_of_surjective
        (X := X) (ι := ι) F hF).inv_hom_id)

theorem symbolicLatentObservationRangeCompHausFunctor_map_isIso_of_surjective_comp
    {S T U : FiniteSymbolicLatentSystem X ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (hg : Function.Surjective g.toFun)
    (hf : Function.Surjective f.toFun) :
    IsIso
      (symbolicLatentObservationRangeCompHausFunctor.map
        (SymbolicLatentMorphism.comp g f)) := by
  have hsurj : Function.Surjective ((SymbolicLatentMorphism.comp g f).toFun) := by
    intro z
    rcases hg z with ⟨y, hy⟩
    rcases hf y with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp [SymbolicLatentMorphism.comp, hy, hx]
  exact symbolicLatentObservationRangeCompHausFunctor_map_isIso_of_surjective
    (X := X) (ι := ι) (SymbolicLatentMorphism.comp g f) hsurj

end

end InfoGeometry.Topology
