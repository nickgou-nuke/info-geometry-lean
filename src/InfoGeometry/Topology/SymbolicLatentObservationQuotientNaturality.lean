import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationQuotientTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Naturality of the observational quotient readout

The quotient map induced by a symbolic-latent morphism preserves the native
observation readout.  The resulting square is exposed in `TopCat`.
-/

theorem symbolicObservationQuotientMap_quotientMap
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    symbolicObservationQuotientMap T (F.quotientMap q) =
      symbolicObservationQuotientMap S q := by
  refine _root_.Quotient.inductionOn q ?_
  intro x
  funext i
  change (T.observable i) (F.toFun x) = (S.observable i) x
  exact F.intertwines i x

def symbolicLatentMorphismQuotientTopCatHom
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    TopCat.of (_root_.Quotient (symbolicObservationalSetoid S)) ⟶
      TopCat.of (_root_.Quotient (symbolicObservationalSetoid T)) :=
  TopCat.ofHom
    { toFun := F.quotientMap
      continuous_toFun := F.continuous_quotientMap }

theorem symbolicLatentMorphismQuotientTopCatHom_apply
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    symbolicLatentMorphismQuotientTopCatHom F q = F.quotientMap q :=
  rfl

theorem symbolicObservationQuotientTopCatHom_natural
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    symbolicLatentMorphismQuotientTopCatHom F ≫
        symbolicObservationQuotientTopCatHom T =
      symbolicObservationQuotientTopCatHom S := by
  ext q i
  change (symbolicObservationQuotientMap T (F.quotientMap q)) i =
    (symbolicObservationQuotientMap S q) i
  exact congrFun (symbolicObservationQuotientMap_quotientMap F q) i

theorem symbolicObservationQuotientTopCatHom_natural_comp
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    symbolicLatentMorphismQuotientTopCatHom
        (SymbolicLatentMorphism.comp g f) ≫
        symbolicObservationQuotientTopCatHom U =
      symbolicObservationQuotientTopCatHom S := by
  exact symbolicObservationQuotientTopCatHom_natural
    (SymbolicLatentMorphism.comp g f)

def symbolicObservationQuotientRangeMapOfMorphism
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    Set.range (symbolicObservationQuotientMap S) →
      Set.range (symbolicObservationQuotientMap T) :=
  fun y =>
    ⟨y.1, by
      rcases y.2 with ⟨q, hq⟩
      refine ⟨F.quotientMap q, ?_⟩
      rw [symbolicObservationQuotientMap_quotientMap F q]
      exact hq⟩

theorem continuous_symbolicObservationQuotientRangeMapOfMorphism
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    Continuous (symbolicObservationQuotientRangeMapOfMorphism F) := by
  exact continuous_subtype_val.subtype_mk (fun y => by
    rcases y.2 with ⟨q, hq⟩
    refine ⟨F.quotientMap q, ?_⟩
    rw [symbolicObservationQuotientMap_quotientMap F q]
    exact hq)

def symbolicObservationQuotientRangeMapOfMorphismTopCatHom
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    TopCat.of (Set.range (symbolicObservationQuotientMap S)) ⟶
      TopCat.of (Set.range (symbolicObservationQuotientMap T)) :=
  TopCat.ofHom
    { toFun := symbolicObservationQuotientRangeMapOfMorphism F
      continuous_toFun := continuous_symbolicObservationQuotientRangeMapOfMorphism F }

theorem symbolicObservationQuotientRangeMapOfMorphism_inclusion_natural
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    symbolicObservationQuotientRangeMapOfMorphismTopCatHom F ≫
        symbolicObservationQuotientRangeInclusionTopCatHom T =
      symbolicObservationQuotientRangeInclusionTopCatHom S := by
  ext y
  rfl

theorem symbolicObservationQuotientRangeMapOfMorphism_quotient_natural
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T) :
    symbolicObservationQuotientRangeTopCatHom S ≫
        symbolicObservationQuotientRangeMapOfMorphismTopCatHom F =
      symbolicLatentMorphismQuotientTopCatHom F ≫
        symbolicObservationQuotientRangeTopCatHom T := by
  ext q i
  change (symbolicObservationQuotientMap S q) i =
    (symbolicObservationQuotientMap T (F.quotientMap q)) i
  exact (congrFun (symbolicObservationQuotientMap_quotientMap F q) i).symm

theorem symbolicObservationQuotientRangeMapOfMorphism_id
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicObservationQuotientRangeMapOfMorphism
        (SymbolicLatentMorphism.id S) = id := by
  funext y
  apply Subtype.ext
  rfl

theorem symbolicObservationQuotientRangeMapOfMorphism_comp
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    symbolicObservationQuotientRangeMapOfMorphism
        (SymbolicLatentMorphism.comp g f) =
      (symbolicObservationQuotientRangeMapOfMorphism g) ∘
        (symbolicObservationQuotientRangeMapOfMorphism f) := by
  funext y
  apply Subtype.ext
  rfl

theorem symbolicObservationQuotientRange_eq_of_surjective
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun) :
    Set.range (symbolicObservationQuotientMap S) =
      Set.range (symbolicObservationQuotientMap T) := by
  ext y
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨F.quotientMap q, ?_⟩
    rw [symbolicObservationQuotientMap_quotientMap F q]
    exact hq
  · rintro ⟨q, hq⟩
    revert hq
    refine _root_.Quotient.inductionOn q ?_
    intro x hq
    rcases hF x with ⟨x', hx'⟩
    refine ⟨_root_.Quotient.mk (symbolicObservationalSetoid S) x', ?_⟩
    calc
      symbolicObservationQuotientMap S
          (_root_.Quotient.mk (symbolicObservationalSetoid S) x') =
          symbolicObservationQuotientMap T
            (F.quotientMap
              (_root_.Quotient.mk (symbolicObservationalSetoid S) x')) :=
        (symbolicObservationQuotientMap_quotientMap F
          (_root_.Quotient.mk (symbolicObservationalSetoid S) x')).symm
      _ = symbolicObservationQuotientMap T
          (_root_.Quotient.mk (symbolicObservationalSetoid T) x) := by
        simp [SymbolicLatentMorphism.quotientMap_mk, hx']
      _ = y := hq

noncomputable def symbolicObservationQuotientRangeHomeomorphOfMorphism
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (hrange : Set.range (symbolicObservationQuotientMap S) =
      Set.range (symbolicObservationQuotientMap T)) :
    Set.range (symbolicObservationQuotientMap S) ≃ₜ
      Set.range (symbolicObservationQuotientMap T) :=
  Homeomorph.setCongr hrange

theorem symbolicObservationQuotientRangeMapOfMorphism_eq_homeomorph
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T)
    (hrange : Set.range (symbolicObservationQuotientMap S) =
      Set.range (symbolicObservationQuotientMap T)) :
    symbolicObservationQuotientRangeMapOfMorphism F =
      (symbolicObservationQuotientRangeHomeomorphOfMorphism hrange).toFun := by
  funext y
  apply Subtype.ext
  rfl

noncomputable def symbolicObservationQuotientRangeInverseOfMorphismTopCatHom
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (hrange : Set.range (symbolicObservationQuotientMap S) =
      Set.range (symbolicObservationQuotientMap T)) :
    TopCat.of (Set.range (symbolicObservationQuotientMap T)) ⟶
      TopCat.of (Set.range (symbolicObservationQuotientMap S)) :=
    TopCat.ofHom
    { toFun := (symbolicObservationQuotientRangeHomeomorphOfMorphism hrange).symm
      continuous_toFun :=
        (symbolicObservationQuotientRangeHomeomorphOfMorphism hrange).symm.continuous_toFun }

theorem symbolicObservationQuotientRangeMapOfMorphismTopCatHom_isIso_of_range_eq
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T)
    (hrange : Set.range (symbolicObservationQuotientMap S) =
      Set.range (symbolicObservationQuotientMap T)) :
    IsIso (symbolicObservationQuotientRangeMapOfMorphismTopCatHom F) := by
  let e := symbolicObservationQuotientRangeHomeomorphOfMorphism hrange
  refine IsIso.mk ⟨symbolicObservationQuotientRangeInverseOfMorphismTopCatHom hrange, ?_, ?_⟩
  · apply TopCat.hom_ext
    simp only [symbolicObservationQuotientRangeInverseOfMorphismTopCatHom,
      symbolicObservationQuotientRangeMapOfMorphismTopCatHom,
      TopCat.hom_comp, TopCat.hom_id, TopCat.hom_ofHom]
    apply ContinuousMap.ext
    intro y
    dsimp
    change e.symm (e y) = y
    exact e.symm_apply_apply y
  · apply TopCat.hom_ext
    simp only [symbolicObservationQuotientRangeInverseOfMorphismTopCatHom,
      symbolicObservationQuotientRangeMapOfMorphismTopCatHom,
      TopCat.hom_comp, TopCat.hom_id, TopCat.hom_ofHom]
    apply ContinuousMap.ext
    intro y
    dsimp
    change e (e.symm y) = y
    exact e.apply_symm_apply y

theorem symbolicObservationQuotientRangeMapOfMorphismTopCatHom_id
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicObservationQuotientRangeMapOfMorphismTopCatHom
        (SymbolicLatentMorphism.id S) =
      𝟙 (TopCat.of (Set.range (symbolicObservationQuotientMap S))) := by
  ext y
  rfl

theorem symbolicObservationQuotientRangeMapOfMorphismTopCatHom_comp
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
  ext y
  rfl

theorem symbolicObservationQuotientRangeMapOfMorphismTopCatHom_comp_apply
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (y : Set.range (symbolicObservationQuotientMap S)) :
    symbolicObservationQuotientRangeMapOfMorphismTopCatHom
        (SymbolicLatentMorphism.comp g f) y =
      (symbolicObservationQuotientRangeMapOfMorphismTopCatHom f ≫
        symbolicObservationQuotientRangeMapOfMorphismTopCatHom g) y := by
  exact congrArg (fun m => m y)
    (symbolicObservationQuotientRangeMapOfMorphismTopCatHom_comp g f)

theorem symbolicObservationQuotientRangeMapOfMorphismTopCatHom_isIso_of_surjective
    {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentMorphism S T)
    (hF : Function.Surjective F.toFun) :
    IsIso (symbolicObservationQuotientRangeMapOfMorphismTopCatHom F) := by
  exact symbolicObservationQuotientRangeMapOfMorphismTopCatHom_isIso_of_range_eq F
    (symbolicObservationQuotientRange_eq_of_surjective F hF)

theorem symbolicObservationQuotientRangeMapOfMorphismTopCatHom_isIso_comp
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (hg : Function.Surjective g.toFun)
    (hf : Function.Surjective f.toFun) :
    IsIso
      (symbolicObservationQuotientRangeMapOfMorphismTopCatHom
        (SymbolicLatentMorphism.comp g f)) := by
  have hsurj : Function.Surjective ((SymbolicLatentMorphism.comp g f).toFun) := by
    intro z
    rcases hg z with ⟨y, hy⟩
    rcases hf y with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp [SymbolicLatentMorphism.comp, hy, hx]
  exact symbolicObservationQuotientRangeMapOfMorphismTopCatHom_isIso_of_surjective
    (SymbolicLatentMorphism.comp g f) hsurj

theorem symbolicLatentMorphismQuotientTopCatHom_id
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicLatentMorphismQuotientTopCatHom
        (SymbolicLatentMorphism.id S) =
      𝟙 (TopCat.of (_root_.Quotient (symbolicObservationalSetoid S))) := by
  ext q
  refine _root_.Quotient.inductionOn q ?_
  intro x
  rfl

theorem symbolicLatentMorphismQuotientTopCatHom_comp
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T) :
    symbolicLatentMorphismQuotientTopCatHom
        (SymbolicLatentMorphism.comp g f) =
      symbolicLatentMorphismQuotientTopCatHom f ≫
        symbolicLatentMorphismQuotientTopCatHom g := by
  ext q
  refine _root_.Quotient.inductionOn q ?_
  intro x
  rfl

theorem symbolicLatentMorphismQuotientTopCatHom_comp_apply
    {X Y Z ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (g : SymbolicLatentMorphism T U)
    (f : SymbolicLatentMorphism S T)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    symbolicLatentMorphismQuotientTopCatHom
        (SymbolicLatentMorphism.comp g f) q =
      (symbolicLatentMorphismQuotientTopCatHom f ≫
        symbolicLatentMorphismQuotientTopCatHom g) q := by
  exact congrArg (fun m => m q)
    (symbolicLatentMorphismQuotientTopCatHom_comp g f)

end InfoGeometry.Topology
