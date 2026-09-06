import InfoGeometry.Topology.SymbolicLatentObservationQuotientCompHaus
import InfoGeometry.Topology.SymbolicLatentObservationRangeCompHausFunctor

/-!
# The observational quotient as a compact-Hausdorff functor

For a compact latent carrier, quotient carriers and their observation ranges
form two `CompHaus`-valued readouts of the same symbolic-latent category.
This owner packages the quotient-side functor and the canonical natural
isomorphism from quotient carriers to feature-readout ranges.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

noncomputable def symbolicObservationQuotientCompHausHomOfMorphism
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T) :
    symbolicObservationQuotientCompHaus S ⟶
      symbolicObservationQuotientCompHaus T := by
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap S)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range S)
  letI : T2Space (Set.range (symbolicObservationQuotientMap S)) := inferInstance
  letI : CompactSpace (_root_.Quotient (symbolicObservationalSetoid S)) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.compactSpace
  letI : T2Space (_root_.Quotient (symbolicObservationalSetoid S)) :=
    (symbolicObservationQuotientRangeCompactHomeomorph S).symm.t2Space
  letI : CompactSpace (Set.range (symbolicObservationQuotientMap T)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range T)
  letI : T2Space (Set.range (symbolicObservationQuotientMap T)) := inferInstance
  letI : CompactSpace (_root_.Quotient (symbolicObservationalSetoid T)) :=
    (symbolicObservationQuotientRangeCompactHomeomorph T).symm.compactSpace
  letI : T2Space (_root_.Quotient (symbolicObservationalSetoid T)) :=
    (symbolicObservationQuotientRangeCompactHomeomorph T).symm.t2Space
  dsimp [symbolicObservationQuotientCompHaus]
  change CompHaus.of (_root_.Quotient (symbolicObservationalSetoid S)) ⟶
    CompHaus.of (_root_.Quotient (symbolicObservationalSetoid T))
  exact ⟨TopCat.ofHom
    { toFun := F.quotientMap
      continuous_toFun := F.continuous_quotientMap }⟩

theorem symbolicObservationQuotientCompHausHomOfMorphism_apply
    {S T : FiniteSymbolicLatentSystem X ι}
    (F : SymbolicLatentMorphism S T)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    symbolicObservationQuotientCompHausHomOfMorphism F q =
      F.quotientMap q :=
  by
    change F.quotientMap q = F.quotientMap q
    rfl

theorem symbolicObservationQuotientCompHausHomOfMorphism_id
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicObservationQuotientCompHausHomOfMorphism
        (SymbolicLatentMorphism.id S) =
      𝟙 (symbolicObservationQuotientCompHaus S) := by
  apply ConcreteCategory.hom_ext
  intro q
  change (SymbolicLatentMorphism.id S).quotientMap q = q
  exact congrFun (SymbolicLatentMorphism.quotientMap_id (S := S)) q

theorem symbolicObservationQuotientCompHausHomOfMorphism_comp
    {S T U : FiniteSymbolicLatentSystem X ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    symbolicObservationQuotientCompHausHomOfMorphism
        (SymbolicLatentMorphism.comp g f) =
      symbolicObservationQuotientCompHausHomOfMorphism f ≫
        symbolicObservationQuotientCompHausHomOfMorphism g := by
  apply ConcreteCategory.hom_ext
  intro q
  change (SymbolicLatentMorphism.comp g f).quotientMap q =
    g.quotientMap (f.quotientMap q)
  exact congrFun (SymbolicLatentMorphism.quotientMap_comp g f) q

noncomputable def symbolicObservationQuotientCompHausFunctor :
    (FiniteSymbolicLatentSystem X ι) ⥤ CompHaus where
  obj S := symbolicObservationQuotientCompHaus S
  map F := symbolicObservationQuotientCompHausHomOfMorphism F
  map_id S := symbolicObservationQuotientCompHausHomOfMorphism_id S
  map_comp f g := symbolicObservationQuotientCompHausHomOfMorphism_comp g f

noncomputable def symbolicObservationQuotientRangeCompHausNaturalIso :
    symbolicObservationQuotientCompHausFunctor (X := X) (ι := ι) ≅
      symbolicLatentObservationRangeCompHausFunctor (X := X) (ι := ι) :=
  NatIso.ofComponents
    (fun S => symbolicObservationQuotientCompHausIso S)
    (by
      intro S T F
      apply ConcreteCategory.hom_ext
      intro q
      apply Subtype.ext
      exact symbolicObservationQuotientMap_quotientMap F q)

theorem symbolicObservationQuotientRangeCompHausNaturalIso_app_hom
    (S : FiniteSymbolicLatentSystem X ι) :
    (symbolicObservationQuotientRangeCompHausNaturalIso
      (X := X) (ι := ι)).hom.app S =
      (symbolicObservationQuotientCompHausIso S).hom :=
  rfl

theorem symbolicObservationQuotientRangeCompHausNaturalIso_hom_inv_id
    (S : FiniteSymbolicLatentSystem X ι) :
    (symbolicObservationQuotientRangeCompHausNaturalIso
      (X := X) (ι := ι)).hom.app S ≫
        (symbolicObservationQuotientRangeCompHausNaturalIso
          (X := X) (ι := ι)).inv.app S =
      𝟙 (symbolicObservationQuotientCompHaus S) := by
  exact congrArg (fun α => α.app S)
    ((symbolicObservationQuotientRangeCompHausNaturalIso
      (X := X) (ι := ι)).hom_inv_id)

theorem symbolicObservationQuotientRangeCompHausNaturalIso_inv_hom_id
    (S : FiniteSymbolicLatentSystem X ι) :
    (symbolicObservationQuotientRangeCompHausNaturalIso
      (X := X) (ι := ι)).inv.app S ≫
        (symbolicObservationQuotientRangeCompHausNaturalIso
          (X := X) (ι := ι)).hom.app S =
      𝟙 (symbolicObservationRangeCompHaus S) := by
  exact congrArg (fun α => α.app S)
    ((symbolicObservationQuotientRangeCompHausNaturalIso
      (X := X) (ι := ι)).inv_hom_id)

end InfoGeometry.Topology
