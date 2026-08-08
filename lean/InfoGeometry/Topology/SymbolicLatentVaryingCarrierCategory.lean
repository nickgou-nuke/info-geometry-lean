import InfoGeometry.Topology.SymbolicLatentObservationQuotientRangeNaturalTransformation
import InfoGeometry.Topology.SymbolicLatentFeasibleSubspaceTopCat

namespace InfoGeometry.Topology

open CategoryTheory
open CategoryTheory.Limits

/-!
# Varying-carrier symbolic-latent systems

The fixed-carrier category is useful for local calculations.  This owner
bundles the carrier as a `TopCat` object, so a diagram may vary both its
underlying latent space and its topology while retaining one finite
observation index.
-/

structure SymbolicLatentSystemObject (ι : Type) [Fintype ι] where
  carrier : TopCat
  system : FiniteSymbolicLatentSystem carrier ι

structure SymbolicLatentSystemHom
    {ι : Type} [Fintype ι]
    (S T : SymbolicLatentSystemObject ι) where
  toFun : S.carrier → T.carrier
  continuous_toFun : Continuous toFun
  intertwines : ∀ (i : ι) (x : S.carrier),
    (T.system.observable i) (toFun x) =
      (S.system.observable i) x

namespace SymbolicLatentSystemHom

variable {ι : Type} [Fintype ι]

def id (S : SymbolicLatentSystemObject ι) :
    SymbolicLatentSystemHom S S where
  toFun := fun x => x
  continuous_toFun := continuous_id
  intertwines := by intro i x; rfl

def comp {S T U : SymbolicLatentSystemObject ι}
    (g : SymbolicLatentSystemHom T U)
    (f : SymbolicLatentSystemHom S T) :
    SymbolicLatentSystemHom S U where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  intertwines := by
    intro i x
    change (U.system.observable i) (g.toFun (f.toFun x)) =
      (S.system.observable i) x
    rw [g.intertwines, f.intertwines]

@[ext] theorem ext {S T : SymbolicLatentSystemObject ι}
    (f g : SymbolicLatentSystemHom S T)
    (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

end SymbolicLatentSystemHom

instance symbolicLatentVaryingCarrierCategory (ι : Type) [Fintype ι] :
    Category (SymbolicLatentSystemObject ι) where
  Hom S T := SymbolicLatentSystemHom S T
  id := SymbolicLatentSystemHom.id
  comp := fun {S T U} f g => SymbolicLatentSystemHom.comp g f
  id_comp := by
    intro S T F
    apply SymbolicLatentSystemHom.ext
    funext x
    change F.toFun x = F.toFun x
    rfl
  comp_id := by
    intro S T F
    apply SymbolicLatentSystemHom.ext
    funext x
    change (fun y => F.toFun y) x = F.toFun x
    rfl
  assoc := by
    intro R S T U h g f
    apply SymbolicLatentSystemHom.ext
    funext x
    rfl

def SymbolicLatentSystemHom.toNative
    {ι : Type} [Fintype ι]
    {S T : SymbolicLatentSystemObject ι}
    (F : SymbolicLatentSystemHom S T) :
    SymbolicLatentMorphism S.system T.system where
  toFun := F.toFun
  continuous_toFun := F.continuous_toFun
  intertwines := F.intertwines

/-! Feasibility is also functorial when the latent carrier varies. -/

noncomputable def varyingCarrierFeasibleSubspaceFunctor
    (ι : Type) [Fintype ι] (targets : ι → Set ℝ) :
    SymbolicLatentSystemObject ι ⥤ TopCat where
  obj S := TopCat.of (feasibleLatentSubspace S.system targets)
  map F := symbolicLatentFeasibleSubspaceTopCatHom F.toNative targets
  map_id S := by
    exact symbolicLatentFeasibleSubspaceTopCatHom_id S.system targets
  map_comp f g := by
    exact symbolicLatentFeasibleSubspaceTopCatHom_comp
      g.toNative f.toNative targets

noncomputable def varyingCarrierObservationQuotientFunctor
    (ι : Type) [Fintype ι] :
    SymbolicLatentSystemObject ι ⥤ TopCat where
  obj S := TopCat.of (_root_.Quotient
    (symbolicObservationalSetoid S.system))
  map F := symbolicLatentMorphismQuotientTopCatHom F.toNative
  map_id S := by
    apply TopCat.hom_ext
    ext q
    change (SymbolicLatentMorphism.id S.system).quotientMap q = q
    refine _root_.Quotient.inductionOn q ?_
    intro x
    rfl
  map_comp f g := by
    apply TopCat.hom_ext
    ext q
    change (SymbolicLatentMorphism.comp g.toNative f.toNative).quotientMap q =
      g.toNative.quotientMap (f.toNative.quotientMap q)
    refine _root_.Quotient.inductionOn q ?_
    intro x
    rfl

noncomputable def varyingCarrierObservationRangeFunctor
    (ι : Type) [Fintype ι] :
    SymbolicLatentSystemObject ι ⥤ TopCat where
  obj S := TopCat.of (Set.range (symbolicObservationQuotientMap S.system))
  map F := symbolicObservationQuotientRangeMapOfMorphismTopCatHom F.toNative
  map_id S := symbolicObservationQuotientRangeMapOfMorphismTopCatHom_id S.system
  map_comp f g :=
    symbolicObservationQuotientRangeMapOfMorphismTopCatHom_comp
      g.toNative f.toNative

noncomputable def varyingCarrierObservationQuotientRangeNaturalTransformation
    (ι : Type) [Fintype ι] :
    varyingCarrierObservationQuotientFunctor ι ⟶
      varyingCarrierObservationRangeFunctor ι where
  app S := symbolicObservationQuotientRangeTopCatHom S.system
  naturality := by
    intro S T F
    exact (symbolicObservationQuotientRangeMapOfMorphism_quotient_natural
      F.toNative).symm

section IndexedDiagrams

variable {ι : Type} [Fintype ι]
variable {J : Type} [Category J]

noncomputable def indexedQuotientDiagram
    (D : J ⥤ SymbolicLatentSystemObject ι) : J ⥤ TopCat :=
  D ⋙ varyingCarrierObservationQuotientFunctor ι

noncomputable def indexedRangeDiagram
    (D : J ⥤ SymbolicLatentSystemObject ι) : J ⥤ TopCat :=
  D ⋙ varyingCarrierObservationRangeFunctor ι

noncomputable def indexedQuotientRangeNaturalTransformation
    (D : J ⥤ SymbolicLatentSystemObject ι) :
    indexedQuotientDiagram D ⟶ indexedRangeDiagram D :=
  Functor.whiskerLeft D
    (varyingCarrierObservationQuotientRangeNaturalTransformation ι)

theorem indexedQuotientRangeNaturalTransformation_app
    (D : J ⥤ SymbolicLatentSystemObject ι) (j : J) :
    (indexedQuotientRangeNaturalTransformation D).app j =
      symbolicObservationQuotientRangeTopCatHom (D.obj j).system :=
  rfl

noncomputable def indexedQuotientRangeNaturalIso
    (D : J ⥤ SymbolicLatentSystemObject ι)
    (hquot : ∀ j,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj j).system)) :
    indexedQuotientDiagram D ≅ indexedRangeDiagram D :=
  NatIso.ofComponents
    (fun j => by
      letI : IsIso ((indexedQuotientRangeNaturalTransformation D).app j) := by
        rw [indexedQuotientRangeNaturalTransformation_app]
        exact symbolicObservationQuotientRangeTopCatHom_isIso
          (D.obj j).system (hquot j)
      exact asIso ((indexedQuotientRangeNaturalTransformation D).app j))
    (by
      intro j k F
      exact (indexedQuotientRangeNaturalTransformation D).naturality F)

noncomputable def indexedQuotientRangeColimitIso
    (D : J ⥤ SymbolicLatentSystemObject ι)
    (hquot : ∀ j,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj j).system)) :
    colimit (indexedQuotientDiagram D) ≅ colimit (indexedRangeDiagram D) :=
  HasColimit.isoOfNatIso (indexedQuotientRangeNaturalIso D hquot)

theorem indexedQuotientRangeColimitIso_injection
    (D : J ⥤ SymbolicLatentSystemObject ι)
    (hquot : ∀ j,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj j).system))
    (j : J) :
    colimit.ι (indexedQuotientDiagram D) j ≫
        (indexedQuotientRangeColimitIso D hquot).hom =
      (indexedQuotientRangeNaturalIso D hquot).hom.app j ≫
        colimit.ι (indexedRangeDiagram D) j :=
  HasColimit.isoOfNatIso_ι_hom
    (indexedQuotientRangeNaturalIso D hquot) j

noncomputable def indexedRangeAmbientComponent
    (D : J ⥤ SymbolicLatentSystemObject ι) (j : J) :
    (indexedRangeDiagram D).obj j ⟶ TopCat.of (ι → ℝ) :=
  symbolicObservationQuotientRangeInclusionTopCatHom
    (D.obj j).system

noncomputable def indexedQuotientAmbientComponent
    (D : J ⥤ SymbolicLatentSystemObject ι) (j : J) :
    (indexedQuotientDiagram D).obj j ⟶ TopCat.of (ι → ℝ) :=
  symbolicObservationQuotientTopCatHom (D.obj j).system

noncomputable def indexedRangeAmbientCocone
    (D : J ⥤ SymbolicLatentSystemObject ι) :
    Cocone (indexedRangeDiagram D) where
  pt := TopCat.of (ι → ℝ)
  ι := { app := indexedRangeAmbientComponent D
         naturality := by
           intro j k F
           exact symbolicObservationQuotientRangeMapOfMorphism_inclusion_natural
             (D.map F).toNative }

noncomputable def indexedRangeAmbientReadout
    (D : J ⥤ SymbolicLatentSystemObject ι) :
    colimit (indexedRangeDiagram D) ⟶ (indexedRangeAmbientCocone D).pt :=
  colimit.desc (indexedRangeDiagram D) (indexedRangeAmbientCocone D)

theorem indexedRangeAmbientReadout_stage
    (D : J ⥤ SymbolicLatentSystemObject ι) (j : J) :
    colimit.ι (indexedRangeDiagram D) j ≫ indexedRangeAmbientReadout D =
      (indexedRangeAmbientCocone D).ι.app j :=
  colimit.ι_desc (indexedRangeAmbientCocone D) j

theorem indexedRangeAmbientReadout_unique
    (D : J ⥤ SymbolicLatentSystemObject ι)
    {u v : colimit (indexedRangeDiagram D) ⟶
      (indexedRangeAmbientCocone D).pt}
    (hu : ∀ j, colimit.ι (indexedRangeDiagram D) j ≫ u =
      (indexedRangeAmbientCocone D).ι.app j)
    (hv : ∀ j, colimit.ι (indexedRangeDiagram D) j ≫ v =
      (indexedRangeAmbientCocone D).ι.app j) :
    u = v := by
  apply colimit.hom_ext
  intro j
  rw [hu j, hv j]

noncomputable def indexedQuotientAmbientCocone
    (D : J ⥤ SymbolicLatentSystemObject ι) :
    Cocone (indexedQuotientDiagram D) where
  pt := TopCat.of (ι → ℝ)
  ι := { app := indexedQuotientAmbientComponent D
         naturality := by
           intro j k F
           exact symbolicObservationQuotientTopCatHom_natural
             (D.map F).toNative }

noncomputable def indexedQuotientAmbientReadout
    (D : J ⥤ SymbolicLatentSystemObject ι) :
    colimit (indexedQuotientDiagram D) ⟶ (indexedQuotientAmbientCocone D).pt :=
  colimit.desc (indexedQuotientDiagram D) (indexedQuotientAmbientCocone D)

theorem indexedQuotientAmbientReadout_stage
    (D : J ⥤ SymbolicLatentSystemObject ι) (j : J) :
    colimit.ι (indexedQuotientDiagram D) j ≫
        indexedQuotientAmbientReadout D =
      (indexedQuotientAmbientCocone D).ι.app j :=
  colimit.ι_desc (indexedQuotientAmbientCocone D) j

theorem indexedQuotientAmbientReadout_unique
    (D : J ⥤ SymbolicLatentSystemObject ι)
    {u v : colimit (indexedQuotientDiagram D) ⟶
      (indexedQuotientAmbientCocone D).pt}
    (hu : ∀ j, colimit.ι (indexedQuotientDiagram D) j ≫ u =
      (indexedQuotientAmbientCocone D).ι.app j)
    (hv : ∀ j, colimit.ι (indexedQuotientDiagram D) j ≫ v =
      (indexedQuotientAmbientCocone D).ι.app j) :
    u = v := by
  apply colimit.hom_ext
  intro j
  rw [hu j, hv j]

theorem indexedQuotientAmbientReadout_viaRange
    (D : J ⥤ SymbolicLatentSystemObject ι)
    (hquot : ∀ j,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj j).system)) :
    indexedQuotientAmbientReadout D =
      (indexedQuotientRangeColimitIso D hquot).hom ≫
      indexedRangeAmbientReadout D := by
  apply indexedQuotientAmbientReadout_unique D
    (u := indexedQuotientAmbientReadout D)
    (v := (indexedQuotientRangeColimitIso D hquot).hom ≫
      indexedRangeAmbientReadout D)
  · intro j
    exact indexedQuotientAmbientReadout_stage D j
  · intro j
    rw [← Category.assoc,
      indexedQuotientRangeColimitIso_injection D hquot j,
      Category.assoc, indexedRangeAmbientReadout_stage D j]
    apply TopCat.hom_ext
    ext q
    refine _root_.Quotient.inductionOn q ?_
    intro x
    rfl

theorem indexedQuotientAmbientReadout_viaRange_stage
    (D : J ⥤ SymbolicLatentSystemObject ι)
    (hquot : ∀ j,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj j).system))
    (j : J) :
    colimit.ι (indexedQuotientDiagram D) j ≫
        indexedQuotientAmbientReadout D =
      (indexedQuotientRangeNaturalTransformation D).app j ≫
        colimit.ι (indexedRangeDiagram D) j ≫
          indexedRangeAmbientReadout D := by
  have hvr := indexedQuotientAmbientReadout_viaRange D hquot
  rw [hvr]
  rw [← Category.assoc,
    indexedQuotientRangeColimitIso_injection D hquot j,
    Category.assoc,
    indexedRangeAmbientReadout_stage D j]
  apply TopCat.hom_ext
  ext q
  refine _root_.Quotient.inductionOn q ?_
  intro x
  rfl

/-! A filtered-index property layer.  The `IsFiltered` property is kept as
metadata; all colimit statements are inherited from the generic indexed
bridge above, without adding any unsupported closure or convergence claim. -/
structure FilteredIndexedSymbolicLatentDiagram (J : Type) [Category J]
    (ι : Type) [Fintype ι] where
  diagram : J ⥤ SymbolicLatentSystemObject ι
  filtered : IsFiltered J

namespace FilteredIndexedSymbolicLatentDiagram

variable {J : Type} [Category J]
variable {ι : Type} [Fintype ι]

noncomputable def quotientAmbientReadout
    (D : FilteredIndexedSymbolicLatentDiagram J ι) :
    colimit (indexedQuotientDiagram (ι := ι) D.diagram) ⟶
      (indexedQuotientAmbientCocone (ι := ι) D.diagram).pt :=
  indexedQuotientAmbientReadout (ι := ι) D.diagram

noncomputable def rangeAmbientReadout
    (D : FilteredIndexedSymbolicLatentDiagram J ι) :
    colimit (indexedRangeDiagram (ι := ι) D.diagram) ⟶
      (indexedRangeAmbientCocone (ι := ι) D.diagram).pt :=
  indexedRangeAmbientReadout (ι := ι) D.diagram

theorem quotientAmbientReadout_stage
    (D : FilteredIndexedSymbolicLatentDiagram J ι) (j : J) :
    colimit.ι (indexedQuotientDiagram (ι := ι) D.diagram) j ≫
        quotientAmbientReadout D =
      (indexedQuotientAmbientCocone (ι := ι) D.diagram).ι.app j :=
  indexedQuotientAmbientReadout_stage (ι := ι) D.diagram j

theorem rangeAmbientReadout_stage
    (D : FilteredIndexedSymbolicLatentDiagram J ι) (j : J) :
    colimit.ι (indexedRangeDiagram (ι := ι) D.diagram) j ≫
        rangeAmbientReadout D =
      (indexedRangeAmbientCocone (ι := ι) D.diagram).ι.app j :=
  indexedRangeAmbientReadout_stage (ι := ι) D.diagram j

theorem quotientAmbientReadout_viaRange
    (D : FilteredIndexedSymbolicLatentDiagram J ι)
    (hquot : ∀ j,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap
          (D.diagram.obj j).system)) :
    quotientAmbientReadout D =
      (indexedQuotientRangeColimitIso D.diagram hquot).hom ≫
        rangeAmbientReadout D :=
  indexedQuotientAmbientReadout_viaRange D.diagram hquot

end FilteredIndexedSymbolicLatentDiagram

end IndexedDiagrams

structure SymbolicLatentSequence (ι : Type) [Fintype ι] where
  obj : ℕ → SymbolicLatentSystemObject ι
  step : ∀ n, SymbolicLatentSystemHom (obj n) (obj (n + 1))

namespace SymbolicLatentSequence

variable {ι : Type} [Fintype ι]

noncomputable def diagram (D : SymbolicLatentSequence ι) :
    ℕ ⥤ SymbolicLatentSystemObject ι :=
  Functor.ofSequence D.step

noncomputable def quotientDiagram (D : SymbolicLatentSequence ι) :
    ℕ ⥤ TopCat :=
  D.diagram ⋙ varyingCarrierObservationQuotientFunctor ι

noncomputable def rangeDiagram (D : SymbolicLatentSequence ι) :
    ℕ ⥤ TopCat :=
  D.diagram ⋙ varyingCarrierObservationRangeFunctor ι

noncomputable def quotientRangeNaturalTransformation
    (D : SymbolicLatentSequence ι) :
    D.quotientDiagram ⟶ D.rangeDiagram :=
  Functor.whiskerLeft D.diagram
    (varyingCarrierObservationQuotientRangeNaturalTransformation ι)

theorem quotientRangeNaturalTransformation_app
    (D : SymbolicLatentSequence ι) (n : ℕ) :
    (D.quotientRangeNaturalTransformation.app n) =
      symbolicObservationQuotientRangeTopCatHom (D.obj n).system :=
  rfl

noncomputable def quotientRangeNaturalIso
    (D : SymbolicLatentSequence ι)
    (hquot : ∀ n,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj n).system)) :
    D.quotientDiagram ≅ D.rangeDiagram :=
  NatIso.ofComponents
    (fun n => by
      letI : IsIso (D.quotientRangeNaturalTransformation.app n) := by
        rw [quotientRangeNaturalTransformation_app]
        exact symbolicObservationQuotientRangeTopCatHom_isIso
          (D.obj n).system (hquot n)
      exact asIso (D.quotientRangeNaturalTransformation.app n))
    (by
      intro n m F
      exact D.quotientRangeNaturalTransformation.naturality F)

noncomputable def colimitIso
    (D : SymbolicLatentSequence ι)
    (hquot : ∀ n,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj n).system)) :
    colimit D.quotientDiagram ≅ colimit D.rangeDiagram :=
  HasColimit.isoOfNatIso (D.quotientRangeNaturalIso hquot)

theorem colimitIso_injection
    (D : SymbolicLatentSequence ι)
    (hquot : ∀ n,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj n).system))
    (n : ℕ) :
    colimit.ι D.quotientDiagram n ≫ (D.colimitIso hquot).hom =
      (D.quotientRangeNaturalIso hquot).hom.app n ≫
        colimit.ι D.rangeDiagram n :=
  HasColimit.isoOfNatIso_ι_hom (D.quotientRangeNaturalIso hquot) n

theorem colimitIso_injection_apply
    (D : SymbolicLatentSequence ι)
    (hquot : ∀ n,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj n).system))
    (n : ℕ) (q : (D.quotientDiagram.obj n : TopCat)) :
    (D.colimitIso hquot).hom
        ((colimit.ι D.quotientDiagram n) q) =
      (colimit.ι D.rangeDiagram n)
        ((D.quotientRangeNaturalIso hquot).hom.app n q) := by
  exact congrArg (fun f => f q) (D.colimitIso_injection hquot n)

noncomputable def rangeAmbientCocone
    (D : SymbolicLatentSequence ι) :
  Cocone D.rangeDiagram where
  pt := TopCat.of (ι → ℝ)
  ι := { app := fun n =>
      (symbolicObservationQuotientRangeInclusionTopCatHom
        (D.obj n).system),
         naturality := by
           intro n m F
           exact symbolicObservationQuotientRangeMapOfMorphism_inclusion_natural
             (D.diagram.map F).toNative }

noncomputable def rangeAmbientReadout
    (D : SymbolicLatentSequence ι) :
    colimit D.rangeDiagram ⟶ D.rangeAmbientCocone.pt :=
  colimit.desc D.rangeDiagram D.rangeAmbientCocone

theorem rangeAmbientReadout_stage
    (D : SymbolicLatentSequence ι) (n : ℕ) :
    colimit.ι D.rangeDiagram n ≫ D.rangeAmbientReadout =
      D.rangeAmbientCocone.ι.app n :=
  colimit.ι_desc D.rangeAmbientCocone n

theorem rangeAmbientReadout_stage_apply
    (D : SymbolicLatentSequence ι) (n : ℕ)
    (q : (D.rangeDiagram.obj n : TopCat)) :
    D.rangeAmbientReadout
        ((colimit.ι D.rangeDiagram n) q) =
      (D.rangeAmbientCocone.ι.app n) q := by
  exact congrArg (fun f => f q) (D.rangeAmbientReadout_stage n)

theorem rangeAmbientReadout_unique
    (D : SymbolicLatentSequence ι)
    {u v : colimit D.rangeDiagram ⟶ D.rangeAmbientCocone.pt}
    (hu : ∀ n, colimit.ι D.rangeDiagram n ≫ u =
      D.rangeAmbientCocone.ι.app n)
    (hv : ∀ n, colimit.ι D.rangeDiagram n ≫ v =
      D.rangeAmbientCocone.ι.app n) :
    u = v := by
  apply colimit.hom_ext
  intro n
  rw [hu n, hv n]

noncomputable def quotientAmbientCocone
    (D : SymbolicLatentSequence ι) :
  Cocone D.quotientDiagram where
  pt := D.rangeAmbientCocone.pt
  ι := { app := fun n =>
      symbolicObservationQuotientTopCatHom (D.obj n).system,
         naturality := by
           intro n m F
           exact symbolicObservationQuotientTopCatHom_natural
             (D.diagram.map F).toNative }

noncomputable def quotientAmbientReadout
    (D : SymbolicLatentSequence ι) :
    colimit D.quotientDiagram ⟶ D.quotientAmbientCocone.pt :=
  colimit.desc D.quotientDiagram D.quotientAmbientCocone

theorem quotientAmbientReadout_stage
    (D : SymbolicLatentSequence ι) (n : ℕ) :
    colimit.ι D.quotientDiagram n ≫ D.quotientAmbientReadout =
      D.quotientAmbientCocone.ι.app n :=
  colimit.ι_desc D.quotientAmbientCocone n

theorem quotientAmbientReadout_stage_apply
    (D : SymbolicLatentSequence ι) (n : ℕ)
    (q : (D.quotientDiagram.obj n : TopCat)) :
    D.quotientAmbientReadout
        ((colimit.ι D.quotientDiagram n) q) =
      (D.quotientAmbientCocone.ι.app n) q := by
  exact congrArg (fun f => f q) (D.quotientAmbientReadout_stage n)

theorem quotientAmbientReadout_unique
    (D : SymbolicLatentSequence ι)
    {u v : colimit D.quotientDiagram ⟶ D.quotientAmbientCocone.pt}
    (hu : ∀ n, colimit.ι D.quotientDiagram n ≫ u =
      D.quotientAmbientCocone.ι.app n)
    (hv : ∀ n, colimit.ι D.quotientDiagram n ≫ v =
      D.quotientAmbientCocone.ι.app n) :
    u = v := by
  apply colimit.hom_ext
  intro n
  rw [hu n, hv n]

theorem quotientAmbientReadout_viaRange
    (D : SymbolicLatentSequence ι)
    (hquot : ∀ n,
      Topology.IsQuotientMap
        (symbolicObservationQuotientRangeMap (D.obj n).system)) :
    D.quotientAmbientReadout =
      (D.colimitIso hquot).hom ≫ D.rangeAmbientReadout := by
  apply D.quotientAmbientReadout_unique
    (u := D.quotientAmbientReadout)
    (v := (D.colimitIso hquot).hom ≫ D.rangeAmbientReadout)
  · intro n
    exact D.quotientAmbientReadout_stage n
  · intro n
    rw [← Category.assoc, D.colimitIso_injection hquot n,
      Category.assoc, D.rangeAmbientReadout_stage n]
    apply TopCat.hom_ext
    ext q
    refine _root_.Quotient.inductionOn q ?_
    intro x
    rfl

end SymbolicLatentSequence

end InfoGeometry.Topology
