import InfoGeometry.Topology.SymbolicLatentObservationRangeFunctor

namespace InfoGeometry.Topology

open CategoryTheory
open CategoryTheory.Limits

/-!
# Quotient-to-range naturality

The quotient observation readout and its subtype range factorization are
packaged as two `TopCat` functors.  Their canonical factor maps form a
natural transformation; the componentwise square is the native quotient
naturality theorem.
-/

noncomputable def symbolicObservationQuotientFunctor
    {X ι : Type} [TopologicalSpace X] [Fintype ι] :
    (FiniteSymbolicLatentSystem X ι) ⥤ TopCat where
  obj S := TopCat.of (_root_.Quotient (symbolicObservationalSetoid S))
  map F := symbolicLatentMorphismQuotientTopCatHom F
  map_id S := by
    apply TopCat.hom_ext
    ext q
    change (SymbolicLatentMorphism.id S).quotientMap q = q
    refine _root_.Quotient.inductionOn q ?_
    intro x
    rfl
  map_comp f g := by
    apply TopCat.hom_ext
    ext q
    change (SymbolicLatentMorphism.comp g f).quotientMap q =
      g.quotientMap (f.quotientMap q)
    refine _root_.Quotient.inductionOn q ?_
    intro x
    rfl

noncomputable def symbolicObservationQuotientRangeNaturalTransformation
    {X ι : Type} [TopologicalSpace X] [Fintype ι] :
    symbolicObservationQuotientFunctor (X := X) (ι := ι) ⟶
      symbolicObservationQuotientRangeFunctor (X := X) (ι := ι) where
  app S := symbolicObservationQuotientRangeTopCatHom S
  naturality := by
    intro S T F
    exact (symbolicObservationQuotientRangeMapOfMorphism_quotient_natural F).symm

theorem symbolicObservationQuotientRangeNaturalTransformation_app_apply
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    (symbolicObservationQuotientRangeNaturalTransformation
      (X := X) (ι := ι)).app S q =
    symbolicObservationQuotientRangeMap S q :=
  symbolicObservationQuotientRangeTopCatHom_apply S q

theorem symbolicObservationQuotientRangeNaturalTransformation_app_isIso
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (hquot : Topology.IsQuotientMap
      (symbolicObservationQuotientRangeMap S)) :
    IsIso ((symbolicObservationQuotientRangeNaturalTransformation
      (X := X) (ι := ι)).app S) := by
  exact symbolicObservationQuotientRangeTopCatHom_isIso S hquot

noncomputable def symbolicObservationQuotientRangeNaturalIso
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (hquot : ∀ S : FiniteSymbolicLatentSystem X ι,
      Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S)) :
    symbolicObservationQuotientFunctor (X := X) (ι := ι) ≅
      symbolicObservationQuotientRangeFunctor (X := X) (ι := ι) :=
  NatIso.ofComponents
    (fun S => by
      letI : IsIso ((symbolicObservationQuotientRangeNaturalTransformation
        (X := X) (ι := ι)).app S) :=
        symbolicObservationQuotientRangeNaturalTransformation_app_isIso S (hquot S)
      exact asIso ((symbolicObservationQuotientRangeNaturalTransformation
        (X := X) (ι := ι)).app S))
    (by
      intro S T F
      exact (symbolicObservationQuotientRangeNaturalTransformation
        (X := X) (ι := ι)).naturality F)

noncomputable def symbolicObservationQuotientRangeColimitIso
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (hquot : ∀ S : FiniteSymbolicLatentSystem X ι,
      Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S)) :
    colimit (symbolicObservationQuotientFunctor (X := X) (ι := ι)) ≅
      colimit (symbolicObservationQuotientRangeFunctor (X := X) (ι := ι)) :=
  HasColimit.isoOfNatIso (symbolicObservationQuotientRangeNaturalIso hquot)

theorem symbolicObservationQuotientRangeColimitIso_injection
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (hquot : ∀ S : FiniteSymbolicLatentSystem X ι,
      Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S))
    (S : FiniteSymbolicLatentSystem X ι) :
    colimit.ι (symbolicObservationQuotientFunctor (X := X) (ι := ι)) S ≫
        (symbolicObservationQuotientRangeColimitIso hquot).hom =
      (symbolicObservationQuotientRangeNaturalTransformation
        (X := X) (ι := ι)).app S ≫
        colimit.ι (symbolicObservationQuotientRangeFunctor
          (X := X) (ι := ι)) S :=
  HasColimit.isoOfNatIso_ι_hom
    (symbolicObservationQuotientRangeNaturalIso hquot) S

theorem symbolicObservationQuotientRangeColimitIso_injection_inv
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (hquot : ∀ S : FiniteSymbolicLatentSystem X ι,
      Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S))
    (S : FiniteSymbolicLatentSystem X ι) :
    colimit.ι (symbolicObservationQuotientRangeFunctor
          (X := X) (ι := ι)) S ≫
        (symbolicObservationQuotientRangeColimitIso hquot).inv =
      (symbolicObservationQuotientRangeNaturalIso hquot).inv.app S ≫
        colimit.ι (symbolicObservationQuotientFunctor (X := X) (ι := ι)) S :=
  HasColimit.isoOfNatIso_ι_inv
    (symbolicObservationQuotientRangeNaturalIso hquot) S

noncomputable def symbolicObservationQuotientRangeAmbientCocone
    {X ι : Type} [TopologicalSpace X] [Fintype ι] :
    Cocone (symbolicObservationQuotientRangeFunctor (X := X) (ι := ι)) where
  pt := TopCat.of (ι → ℝ)
  ι := { app := fun S => symbolicObservationQuotientRangeInclusionTopCatHom S
         naturality := by
           intro S T F
           exact symbolicObservationQuotientRangeMapOfMorphism_inclusion_natural F }

noncomputable def symbolicObservationQuotientRangeColimitAmbientReadout
    {X ι : Type} [TopologicalSpace X] [Fintype ι] :
    colimit (symbolicObservationQuotientRangeFunctor (X := X) (ι := ι)) ⟶
      TopCat.of (ι → ℝ) :=
  colimit.desc (symbolicObservationQuotientRangeFunctor (X := X) (ι := ι))
    (symbolicObservationQuotientRangeAmbientCocone (X := X) (ι := ι))

theorem symbolicObservationQuotientRangeColimitAmbientReadout_stage
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    colimit.ι (symbolicObservationQuotientRangeFunctor (X := X) (ι := ι)) S ≫
        symbolicObservationQuotientRangeColimitAmbientReadout
      (X := X) (ι := ι) =
      symbolicObservationQuotientRangeInclusionTopCatHom S :=
  colimit.ι_desc
    (symbolicObservationQuotientRangeAmbientCocone (X := X) (ι := ι)) S

theorem symbolicObservationQuotientRangeColimitAmbientReadout_unique
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    {u v : colimit (symbolicObservationQuotientRangeFunctor (X := X) (ι := ι)) ⟶
      TopCat.of (ι → ℝ)}
    (h_u : ∀ S, colimit.ι
      (symbolicObservationQuotientRangeFunctor (X := X) (ι := ι)) S ≫ u =
      symbolicObservationQuotientRangeInclusionTopCatHom S)
    (h_v : ∀ S, colimit.ι
      (symbolicObservationQuotientRangeFunctor (X := X) (ι := ι)) S ≫ v =
      symbolicObservationQuotientRangeInclusionTopCatHom S) :
    u = v := by
  apply colimit.hom_ext
  intro S
  rw [h_u S, h_v S]

noncomputable def symbolicObservationQuotientAmbientCocone
    {X ι : Type} [TopologicalSpace X] [Fintype ι] :
    Cocone (symbolicObservationQuotientFunctor (X := X) (ι := ι)) where
  pt := TopCat.of (ι → ℝ)
  ι := { app := fun S => symbolicObservationQuotientTopCatHom S
         naturality := by
           intro S T F
           exact symbolicObservationQuotientTopCatHom_natural F }

noncomputable def symbolicObservationQuotientColimitAmbientReadout
    {X ι : Type} [TopologicalSpace X] [Fintype ι] :
    colimit (symbolicObservationQuotientFunctor (X := X) (ι := ι)) ⟶
      TopCat.of (ι → ℝ) :=
  colimit.desc (symbolicObservationQuotientFunctor (X := X) (ι := ι))
    (symbolicObservationQuotientAmbientCocone (X := X) (ι := ι))

theorem symbolicObservationQuotientColimitAmbientReadout_stage
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    colimit.ι (symbolicObservationQuotientFunctor (X := X) (ι := ι)) S ≫
        symbolicObservationQuotientColimitAmbientReadout (X := X) (ι := ι) =
      symbolicObservationQuotientTopCatHom S :=
  colimit.ι_desc
    (symbolicObservationQuotientAmbientCocone (X := X) (ι := ι)) S

theorem symbolicObservationQuotientColimitAmbientReadout_unique
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    {u v : colimit (symbolicObservationQuotientFunctor (X := X) (ι := ι)) ⟶
      TopCat.of (ι → ℝ)}
    (h_u : ∀ S, colimit.ι
      (symbolicObservationQuotientFunctor (X := X) (ι := ι)) S ≫ u =
      symbolicObservationQuotientTopCatHom S)
    (h_v : ∀ S, colimit.ι
      (symbolicObservationQuotientFunctor (X := X) (ι := ι)) S ≫ v =
      symbolicObservationQuotientTopCatHom S) :
    u = v := by
  apply colimit.hom_ext
  intro S
  rw [h_u S, h_v S]

noncomputable def symbolicObservationQuotientColimitAmbientReadout_viaRange
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (hquot : ∀ S : FiniteSymbolicLatentSystem X ι,
      Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S)) :
    colimit (symbolicObservationQuotientFunctor (X := X) (ι := ι)) ⟶
      TopCat.of (ι → ℝ) :=
  (symbolicObservationQuotientRangeColimitIso hquot).hom ≫
    symbolicObservationQuotientRangeColimitAmbientReadout (X := X) (ι := ι)

theorem symbolicObservationQuotientColimitAmbientReadout_viaRange_stage
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (hquot : ∀ S : FiniteSymbolicLatentSystem X ι,
      Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S))
    (S : FiniteSymbolicLatentSystem X ι) :
    colimit.ι (symbolicObservationQuotientFunctor (X := X) (ι := ι)) S ≫
        symbolicObservationQuotientColimitAmbientReadout_viaRange hquot =
      (symbolicObservationQuotientRangeNaturalTransformation
        (X := X) (ι := ι)).app S ≫
        symbolicObservationQuotientRangeInclusionTopCatHom S := by
  rw [symbolicObservationQuotientColimitAmbientReadout_viaRange]
  rw [← Category.assoc,
    symbolicObservationQuotientRangeColimitIso_injection hquot S,
    Category.assoc,
    symbolicObservationQuotientRangeColimitAmbientReadout_stage S]

theorem symbolicObservationQuotientColimitAmbientReadout_eq_viaRange
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (hquot : ∀ S : FiniteSymbolicLatentSystem X ι,
      Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S)) :
    symbolicObservationQuotientColimitAmbientReadout (X := X) (ι := ι) =
      symbolicObservationQuotientColimitAmbientReadout_viaRange hquot := by
  apply colimit.hom_ext
  intro S
  rw [symbolicObservationQuotientColimitAmbientReadout_stage,
    symbolicObservationQuotientColimitAmbientReadout_viaRange_stage hquot S]
  simpa [symbolicObservationQuotientRangeNaturalTransformation] using
    (symbolicObservationQuotientTopCatHom_factorization S).symm

theorem symbolicObservationQuotientColimitAmbientReadout_viaRange_unique
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (hquot : ∀ S : FiniteSymbolicLatentSystem X ι,
      Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S))
    {u : colimit (symbolicObservationQuotientFunctor (X := X) (ι := ι)) ⟶
      TopCat.of (ι → ℝ)}
    (hu : ∀ S,
      colimit.ι (symbolicObservationQuotientFunctor (X := X) (ι := ι)) S ≫ u =
        (symbolicObservationQuotientRangeNaturalTransformation
          (X := X) (ι := ι)).app S ≫
          symbolicObservationQuotientRangeInclusionTopCatHom S) :
    u = symbolicObservationQuotientColimitAmbientReadout_viaRange hquot := by
  apply colimit.hom_ext
  intro S
  have huS := hu S
  have hstage := symbolicObservationQuotientColimitAmbientReadout_viaRange_stage hquot S
  exact huS.trans hstage.symm

end InfoGeometry.Topology
