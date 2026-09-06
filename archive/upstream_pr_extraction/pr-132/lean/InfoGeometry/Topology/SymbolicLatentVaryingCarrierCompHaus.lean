import InfoGeometry.Topology.SymbolicLatentVaryingCarrierCategory
import InfoGeometry.Topology.SymbolicLatentObservationRangeCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact Hausdorff restriction of varying-carrier symbolic-latent systems

The varying-carrier owner already supplies the native category, observation
quotients, ranges, and TopCat colimit readouts.  This file restricts that
category by carrying compact/T2 witnesses and lifts only the observation range
to `CompHaus`.  The quotient carrier remains the existing quotient; the
forgetful natural isomorphism is the native range identification.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

structure CompactSymbolicLatentSystemObject (ι : Type) [Fintype ι] where
  systemObject : SymbolicLatentSystemObject ι
  compactSpace : CompactSpace systemObject.carrier
  t2Space : T2Space systemObject.carrier

abbrev CompactSymbolicLatentSystemHom
    {ι : Type} [Fintype ι]
    (S T : CompactSymbolicLatentSystemObject ι) :=
  SymbolicLatentSystemHom S.systemObject T.systemObject

namespace CompactSymbolicLatentSystemHom

variable {ι : Type} [Fintype ι]

abbrev toNative
    {S T : CompactSymbolicLatentSystemObject ι}
    (F : CompactSymbolicLatentSystemHom S T) :
    SymbolicLatentSystemHom S.systemObject T.systemObject :=
  F

def id (S : CompactSymbolicLatentSystemObject ι) :
    CompactSymbolicLatentSystemHom S S :=
  SymbolicLatentSystemHom.id S.systemObject

def comp {S T U : CompactSymbolicLatentSystemObject ι}
    (g : CompactSymbolicLatentSystemHom T U)
    (f : CompactSymbolicLatentSystemHom S T) :
    CompactSymbolicLatentSystemHom S U :=
  SymbolicLatentSystemHom.comp g f

@[ext] theorem ext {S T : CompactSymbolicLatentSystemObject ι}
    (f g : CompactSymbolicLatentSystemHom S T)
    (h : f.toNative = g.toNative) : f = g :=
  h

end CompactSymbolicLatentSystemHom

instance compactSymbolicLatentVaryingCarrierCategory (ι : Type) [Fintype ι] :
    Category (CompactSymbolicLatentSystemObject ι) where
  Hom S T := CompactSymbolicLatentSystemHom S T
  id := CompactSymbolicLatentSystemHom.id
  comp := fun {S T U} f g => CompactSymbolicLatentSystemHom.comp g f
  id_comp := by
    intro S T F
    apply CompactSymbolicLatentSystemHom.ext
    exact SymbolicLatentSystemHom.ext _ _ rfl
  comp_id := by
    intro S T F
    apply CompactSymbolicLatentSystemHom.ext
    exact SymbolicLatentSystemHom.ext _ _ rfl
  assoc := by
    intro R S T U h g f
    apply CompactSymbolicLatentSystemHom.ext
    exact SymbolicLatentSystemHom.ext _ _ rfl

variable {ι : Type} [Fintype ι]

noncomputable def compactSymbolicLatentForget :
    CompactSymbolicLatentSystemObject ι ⥤ SymbolicLatentSystemObject ι where
  obj S := S.systemObject
  map F := F.toNative
  map_id S := rfl
  map_comp f g := rfl

noncomputable def compactSymbolicLatentObservationRangeCompHaus
    (S : CompactSymbolicLatentSystemObject ι) : CompHaus := by
  letI : CompactSpace S.systemObject.carrier := S.compactSpace
  exact symbolicObservationRangeCompHaus S.systemObject.system

noncomputable def compactSymbolicLatentObservationRangeCompHausTopCatHom
    (S : CompactSymbolicLatentSystemObject ι) :
    TopCat.of (_root_.Quotient
      (symbolicObservationalSetoid S.systemObject.system)) ⟶
      compHausToTop.obj (compactSymbolicLatentObservationRangeCompHaus S) := by
  letI : CompactSpace S.systemObject.carrier := S.compactSpace
  change TopCat.of (_root_.Quotient
      (symbolicObservationalSetoid S.systemObject.system)) ⟶
    TopCat.of (Set.range (symbolicObservationQuotientMap S.systemObject.system))
  exact symbolicObservationRangeCompHausTopCatHom S.systemObject.system

theorem compactSymbolicLatentObservationRangeCompHausTopCatHom_isIso
    (S : CompactSymbolicLatentSystemObject ι) :
    IsIso (compactSymbolicLatentObservationRangeCompHausTopCatHom S) := by
  letI : CompactSpace S.systemObject.carrier := S.compactSpace
  change IsIso (symbolicObservationRangeCompHausTopCatHom S.systemObject.system)
  exact symbolicObservationRangeCompHausTopCatHom_isIso S.systemObject.system

noncomputable def compactSymbolicLatentObservationRangeCompHausHom
    {S T : CompactSymbolicLatentSystemObject ι}
    (F : CompactSymbolicLatentSystemHom S T) :
    compactSymbolicLatentObservationRangeCompHaus S ⟶
      compactSymbolicLatentObservationRangeCompHaus T := by
  letI : CompactSpace S.systemObject.carrier := S.compactSpace
  letI : CompactSpace T.systemObject.carrier := T.compactSpace
  exact ⟨TopCat.ofHom
    { toFun := symbolicObservationQuotientRangeMapOfMorphism F.toNative.toNative
      continuous_toFun :=
        continuous_symbolicObservationQuotientRangeMapOfMorphism
          F.toNative.toNative }⟩

theorem compactSymbolicLatentObservationRangeCompHausHom_forget
    {S T : CompactSymbolicLatentSystemObject ι}
    (F : CompactSymbolicLatentSystemHom S T) :
    compHausToTop.map
        (compactSymbolicLatentObservationRangeCompHausHom F) =
      symbolicObservationQuotientRangeMapOfMorphismTopCatHom
        F.toNative.toNative := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  change symbolicObservationQuotientRangeMapOfMorphism
      F.toNative.toNative y =
    symbolicObservationQuotientRangeMapOfMorphism
      F.toNative.toNative y
  rfl

noncomputable def compactSymbolicLatentObservationRangeCompHausFunctor :
    CompactSymbolicLatentSystemObject ι ⥤ CompHaus where
  obj S := by
    letI : CompactSpace S.systemObject.carrier := S.compactSpace
    exact symbolicObservationRangeCompHaus S.systemObject.system
  map F := compactSymbolicLatentObservationRangeCompHausHom F
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro y
    dsimp [compactSymbolicLatentObservationRangeCompHausHom,
      CompactSymbolicLatentSystemHom.id]
    change symbolicObservationQuotientRangeMapOfMorphism
      (SymbolicLatentMorphism.id S.systemObject.system) y = y
    exact congrFun
      (symbolicObservationQuotientRangeMapOfMorphism_id
        S.systemObject.system) y
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro y
    dsimp [compactSymbolicLatentObservationRangeCompHausHom,
      CompactSymbolicLatentSystemHom.comp]
    change symbolicObservationQuotientRangeMapOfMorphism
        (SymbolicLatentMorphism.comp g.toNative.toNative f.toNative.toNative) y =
      symbolicObservationQuotientRangeMapOfMorphism g.toNative.toNative
        (symbolicObservationQuotientRangeMapOfMorphism f.toNative.toNative y)
    exact congrFun
      (symbolicObservationQuotientRangeMapOfMorphism_comp
        g.toNative.toNative f.toNative.toNative) y

theorem compactSymbolicLatentObservationRangeCompHausFunctor_map_forget
    {S T : CompactSymbolicLatentSystemObject ι}
    (F : CompactSymbolicLatentSystemHom S T) :
    compHausToTop.map
        ((compactSymbolicLatentObservationRangeCompHausFunctor (ι := ι)).map F) =
      symbolicObservationQuotientRangeMapOfMorphismTopCatHom
        F.toNative.toNative := by
  exact compactSymbolicLatentObservationRangeCompHausHom_forget F

theorem compactSymbolicLatentObservationRangeCompHausFunctor_map_isIso_of_surjective
    {S T : CompactSymbolicLatentSystemObject ι}
    (F : CompactSymbolicLatentSystemHom S T)
    (hF : Function.Surjective F.toNative.toFun) :
    IsIso ((compactSymbolicLatentObservationRangeCompHausFunctor (ι := ι)).map F) := by
  have hIso :
      IsIso (symbolicObservationQuotientRangeMapOfMorphismTopCatHom
        F.toNative.toNative) :=
    symbolicObservationQuotientRangeMapOfMorphismTopCatHom_isIso_of_surjective
      (F := F.toNative.toNative)
      hF
  haveI : IsIso (compHausToTop.map
      ((compactSymbolicLatentObservationRangeCompHausFunctor (ι := ι)).map F)) := by
    simpa [compactSymbolicLatentObservationRangeCompHausFunctor_map_forget]
      using hIso
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  exact hFF.isIso_of_isIso_map
    ((compactSymbolicLatentObservationRangeCompHausFunctor (ι := ι)).map F)

theorem compactSymbolicLatentObservationRangeCompHausFunctor_map_isIso_of_surjective_comp
    {S T U : CompactSymbolicLatentSystemObject ι}
    (g : CompactSymbolicLatentSystemHom T U)
    (f : CompactSymbolicLatentSystemHom S T)
    (hg : Function.Surjective g.toNative.toFun)
    (hf : Function.Surjective f.toNative.toFun) :
    IsIso
      ((compactSymbolicLatentObservationRangeCompHausFunctor (ι := ι)).map
        (CompactSymbolicLatentSystemHom.comp g f)) := by
  have hsurj : Function.Surjective
      ((CompactSymbolicLatentSystemHom.comp g f).toNative.toFun) := by
    intro z
    rcases hg z with ⟨y, hy⟩
    rcases hf y with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change g.toNative.toFun (f.toNative.toFun x) = z
    rw [hx, hy]
  exact compactSymbolicLatentObservationRangeCompHausFunctor_map_isIso_of_surjective
    (ι := ι) (CompactSymbolicLatentSystemHom.comp g f) hsurj

noncomputable def compactSymbolicLatentQuotientRangeNaturalTransformation :
    (compactSymbolicLatentForget ⋙
        varyingCarrierObservationQuotientFunctor ι) ⟶
      (compactSymbolicLatentObservationRangeCompHausFunctor (ι := ι) ⋙
        compHausToTop) where
  app S := by
    exact compactSymbolicLatentObservationRangeCompHausTopCatHom S
  naturality := by
    intro S T F
    exact (symbolicObservationQuotientRangeMapOfMorphism_quotient_natural
      F.toNative.toNative).symm

noncomputable def compactSymbolicLatentQuotientRangeNaturalIso :
    (compactSymbolicLatentForget ⋙
        varyingCarrierObservationQuotientFunctor ι) ≅
      (compactSymbolicLatentObservationRangeCompHausFunctor (ι := ι) ⋙
        compHausToTop) :=
  NatIso.ofComponents
    (fun S => by
      letI : IsIso
          ((compactSymbolicLatentQuotientRangeNaturalTransformation (ι := ι)).app S) := by
        exact compactSymbolicLatentObservationRangeCompHausTopCatHom_isIso S
      exact asIso
        ((compactSymbolicLatentQuotientRangeNaturalTransformation (ι := ι)).app S))
    (by
      intro S T F
      exact (compactSymbolicLatentQuotientRangeNaturalTransformation
        (ι := ι)).naturality F)

theorem compactSymbolicLatentQuotientRangeNaturalIso_app_hom
    (S : CompactSymbolicLatentSystemObject ι) :
    (compactSymbolicLatentQuotientRangeNaturalIso (ι := ι)).hom.app S =
      compactSymbolicLatentObservationRangeCompHausTopCatHom S := by
  rfl

@[simp] theorem compactSymbolicLatentQuotientRangeNaturalIso_hom_inv_id
    (S : CompactSymbolicLatentSystemObject ι) :
    (compactSymbolicLatentQuotientRangeNaturalIso (ι := ι)).hom.app S ≫
        (compactSymbolicLatentQuotientRangeNaturalIso (ι := ι)).inv.app S =
      𝟙
        ((compactSymbolicLatentForget ⋙
            varyingCarrierObservationQuotientFunctor ι).obj S) := by
  exact congrArg (fun α => α.app S)
    ((compactSymbolicLatentQuotientRangeNaturalIso (ι := ι)).hom_inv_id)

@[simp] theorem compactSymbolicLatentQuotientRangeNaturalIso_inv_hom_id
    (S : CompactSymbolicLatentSystemObject ι) :
    (compactSymbolicLatentQuotientRangeNaturalIso (ι := ι)).inv.app S ≫
        (compactSymbolicLatentQuotientRangeNaturalIso (ι := ι)).hom.app S =
      𝟙
        ((compactSymbolicLatentObservationRangeCompHausFunctor (ι := ι) ⋙
            compHausToTop).obj S) := by
  exact congrArg (fun α => α.app S)
    ((compactSymbolicLatentQuotientRangeNaturalIso (ι := ι)).inv_hom_id)

end InfoGeometry.Topology
