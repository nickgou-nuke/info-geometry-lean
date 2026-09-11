import InfoGeometry.Topology.SymbolicLatentVaryingCarrierCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservationQuotientCompHausFunctor

/-!
# Compact-Hausdorff quotient functor for varying-carrier systems

The varying-carrier layer already has a `TopCat` quotient functor and a
`CompHaus` range functor.  This owner packages the quotient itself in
`CompHaus` and upgrades the quotient-to-range comparison to a genuine
`CompHaus` natural isomorphism.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {ι : Type} [Fintype ι]

noncomputable def compactSymbolicLatentObservationQuotientCompHaus
    (S : CompactSymbolicLatentSystemObject ι) : CompHaus := by
  letI : CompactSpace S.systemObject.carrier := S.compactSpace
  exact symbolicObservationQuotientCompHaus S.systemObject.system

noncomputable def compactSymbolicLatentObservationQuotientCompHausHom
    {S T : CompactSymbolicLatentSystemObject ι}
    (F : CompactSymbolicLatentSystemHom S T) :
    compactSymbolicLatentObservationQuotientCompHaus S ⟶
      compactSymbolicLatentObservationQuotientCompHaus T := by
  letI : CompactSpace S.systemObject.carrier := S.compactSpace
  letI : CompactSpace T.systemObject.carrier := T.compactSpace
  letI : CompactSpace (Set.range
      (symbolicObservationQuotientMap S.systemObject.system)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range S.systemObject.system)
  letI : T2Space (Set.range
      (symbolicObservationQuotientMap S.systemObject.system)) := inferInstance
  letI : CompactSpace (_root_.Quotient
      (symbolicObservationalSetoid S.systemObject.system)) :=
    (symbolicObservationQuotientRangeCompactHomeomorph
      S.systemObject.system).symm.compactSpace
  letI : T2Space (_root_.Quotient
      (symbolicObservationalSetoid S.systemObject.system)) :=
    (symbolicObservationQuotientRangeCompactHomeomorph
      S.systemObject.system).symm.t2Space
  letI : CompactSpace (Set.range
      (symbolicObservationQuotientMap T.systemObject.system)) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicObservationQuotient_range T.systemObject.system)
  letI : T2Space (Set.range
      (symbolicObservationQuotientMap T.systemObject.system)) := inferInstance
  letI : CompactSpace (_root_.Quotient
      (symbolicObservationalSetoid T.systemObject.system)) :=
    (symbolicObservationQuotientRangeCompactHomeomorph
      T.systemObject.system).symm.compactSpace
  letI : T2Space (_root_.Quotient
      (symbolicObservationalSetoid T.systemObject.system)) :=
    (symbolicObservationQuotientRangeCompactHomeomorph
      T.systemObject.system).symm.t2Space
  dsimp [compactSymbolicLatentObservationQuotientCompHaus]
  exact ⟨TopCat.ofHom
    { toFun := F.toNative.toNative.quotientMap
      continuous_toFun := F.toNative.toNative.continuous_quotientMap }⟩

@[simp] theorem compactSymbolicLatentObservationQuotientCompHausHom_apply
    {S T : CompactSymbolicLatentSystemObject ι}
    (F : CompactSymbolicLatentSystemHom S T)
    (q : compactSymbolicLatentObservationQuotientCompHaus S) :
    compactSymbolicLatentObservationQuotientCompHausHom F q =
      F.toNative.toNative.quotientMap q := by
  letI : CompactSpace S.systemObject.carrier := S.compactSpace
  letI : CompactSpace T.systemObject.carrier := T.compactSpace
  dsimp [compactSymbolicLatentObservationQuotientCompHausHom,
    compactSymbolicLatentObservationQuotientCompHaus]
  change F.toNative.toNative.quotientMap q =
    F.toNative.toNative.quotientMap q
  rfl

theorem compactSymbolicLatentObservationQuotientCompHausHom_forget
    {S T : CompactSymbolicLatentSystemObject ι}
    (F : CompactSymbolicLatentSystemHom S T) :
    compHausToTop.map
        (compactSymbolicLatentObservationQuotientCompHausHom F) =
      symbolicLatentMorphismQuotientTopCatHom F.toNative.toNative := by
  rfl

noncomputable def compactSymbolicLatentObservationQuotientCompHausFunctor :
    CompactSymbolicLatentSystemObject ι ⥤ CompHaus where
  obj S := compactSymbolicLatentObservationQuotientCompHaus S
  map F := compactSymbolicLatentObservationQuotientCompHausHom F
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro q
    dsimp [compactSymbolicLatentObservationQuotientCompHausHom,
      compactSymbolicLatentObservationQuotientCompHaus,
      CompactSymbolicLatentSystemHom.id]
    change (SymbolicLatentMorphism.id S.systemObject.system).quotientMap q = q
    exact congrFun
      (SymbolicLatentMorphism.quotientMap_id
        (S := S.systemObject.system)) q
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    dsimp [compactSymbolicLatentObservationQuotientCompHausHom,
      compactSymbolicLatentObservationQuotientCompHaus,
      CompactSymbolicLatentSystemHom.comp]
    change (CompactSymbolicLatentSystemHom.comp g f).toNative.toNative.quotientMap q =
      g.toNative.toNative.quotientMap (f.toNative.toNative.quotientMap q)
    exact congrFun
        (SymbolicLatentMorphism.quotientMap_comp
        g.toNative.toNative f.toNative.toNative) q

@[simp] theorem compactSymbolicLatentObservationQuotientCompHausFunctor_map_apply
    {S T : CompactSymbolicLatentSystemObject ι}
    (F : CompactSymbolicLatentSystemHom S T)
    (q : compactSymbolicLatentObservationQuotientCompHaus S) :
    (compactSymbolicLatentObservationQuotientCompHausFunctor (ι := ι)).map F q =
      F.toNative.toNative.quotientMap q := by
  exact compactSymbolicLatentObservationQuotientCompHausHom_apply F q

noncomputable def compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso :
    compactSymbolicLatentObservationQuotientCompHausFunctor (ι := ι) ≅
      compactSymbolicLatentObservationRangeCompHausFunctor (ι := ι) :=
  NatIso.ofComponents
    (fun S => by
      letI : CompactSpace S.systemObject.carrier := S.compactSpace
      exact symbolicObservationQuotientCompHausIso S.systemObject.system)
    (by
      intro S T F
      letI : CompactSpace S.systemObject.carrier := S.compactSpace
      letI : CompactSpace T.systemObject.carrier := T.compactSpace
      have hFF : (compHausToTop).FullyFaithful := by
        simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
      apply hFF.map_injective
      simpa only [Functor.map_comp,
        compactSymbolicLatentObservationQuotientCompHausHom_forget,
        symbolicObservationQuotientCompHausIso_hom_forget,
        compactSymbolicLatentObservationRangeCompHausFunctor_map_forget] using
        (symbolicObservationQuotientRangeMapOfMorphism_quotient_natural
          F.toNative.toNative).symm)

@[simp] theorem compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso_app_hom_apply
    (S : CompactSymbolicLatentSystemObject ι)
    (q : compactSymbolicLatentObservationQuotientCompHaus S) :
    ((compactSymbolicLatentObservationQuotientRangeCompHausNaturalIso
      (ι := ι)).hom.app S) q =
      symbolicObservationQuotientRangeMap S.systemObject.system q := by
  letI : CompactSpace S.systemObject.carrier := S.compactSpace
  rfl

end InfoGeometry.Topology
