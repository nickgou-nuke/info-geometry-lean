import InfoGeometry.Topology.ChiralOperatorQuotientBraidCompHaus

/-!
# Compact-Hausdorff braid transport to the observation range

The quotient braid action is transported to the compact range of the native
operator-valued observation map.  The transport is a genuine `CompHaus`
morphism and its two tensor-factor naturality squares are proved pointwise.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompactSpace A]

abbrev ChiralOperatorObservationRange (A : Type) [NormedRing A]
    [NormedAlgebra ℝ A] :=
  Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap

abbrev ChiralOperatorObservationRangeTensor3 (A : Type) [NormedRing A]
    [NormedAlgebra ℝ A] :=
  ChiralOperatorObservationRange A ×
    ChiralOperatorObservationRange A ×
      ChiralOperatorObservationRange A

noncomputable def chiralOperatorObservationRangeTensor3CompHaus : CompHaus := by
  letI : CompactSpace (ChiralOperatorObservationRange A) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap
        (operatorSageLatentSystem (A := A))))
  exact CompHaus.of (ChiralOperatorObservationRangeTensor3 A)

def chiralOperatorObservationRangeTensorR12
    (p : ChiralOperatorObservationRangeTensor3 A) :
    ChiralOperatorObservationRangeTensor3 A :=
  (p.2.1, p.1, p.2.2)

def chiralOperatorObservationRangeTensorR23
    (p : ChiralOperatorObservationRangeTensor3 A) :
    ChiralOperatorObservationRangeTensor3 A :=
  (p.1, p.2.2, p.2.1)

theorem continuous_chiralOperatorObservationRangeTensorR12 :
    Continuous (chiralOperatorObservationRangeTensorR12 (A := A)) := by
  change Continuous (fun p : ChiralOperatorObservationRangeTensor3 A =>
    (p.2.1, p.1, p.2.2))
  exact (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))

theorem continuous_chiralOperatorObservationRangeTensorR23 :
    Continuous (chiralOperatorObservationRangeTensorR23 (A := A)) := by
  change Continuous (fun p : ChiralOperatorObservationRangeTensor3 A =>
    (p.1, p.2.2, p.2.1))
  exact continuous_fst.prodMk
    ((continuous_snd.comp continuous_snd).prodMk
      (continuous_fst.comp continuous_snd))

noncomputable def chiralOperatorObservationRangeTensorR12Homeomorph :
    ChiralOperatorObservationRangeTensor3 A ≃ₜ
      ChiralOperatorObservationRangeTensor3 A :=
  { toFun := chiralOperatorObservationRangeTensorR12
    invFun := chiralOperatorObservationRangeTensorR12
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := continuous_chiralOperatorObservationRangeTensorR12
    continuous_invFun := continuous_chiralOperatorObservationRangeTensorR12 }

noncomputable def chiralOperatorObservationRangeTensorR23Homeomorph :
    ChiralOperatorObservationRangeTensor3 A ≃ₜ
      ChiralOperatorObservationRangeTensor3 A :=
  { toFun := chiralOperatorObservationRangeTensorR23
    invFun := chiralOperatorObservationRangeTensorR23
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := continuous_chiralOperatorObservationRangeTensorR23
    continuous_invFun := continuous_chiralOperatorObservationRangeTensorR23 }

noncomputable def chiralOperatorObservationRangeTensorR12CompHausIso :
    chiralOperatorObservationRangeTensor3CompHaus (A := A) ≅
      chiralOperatorObservationRangeTensor3CompHaus (A := A) := by
  let e := chiralOperatorObservationRangeTensorR12Homeomorph (A := A)
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro p
        exact e.symm_apply_apply p
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro p
        exact e.apply_symm_apply p }

noncomputable def chiralOperatorObservationRangeTensorR23CompHausIso :
    chiralOperatorObservationRangeTensor3CompHaus (A := A) ≅
      chiralOperatorObservationRangeTensor3CompHaus (A := A) := by
  let e := chiralOperatorObservationRangeTensorR23Homeomorph (A := A)
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro p
        exact e.symm_apply_apply p
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro p
        exact e.apply_symm_apply p }

noncomputable def chiralOperatorQuotientTensor3ObservationRangeHom :
    chiralOperatorQuotientTensor3CompHaus (A := A) ⟶
      chiralOperatorObservationRangeTensor3CompHaus (A := A) := by
  letI : CompactSpace (Set.range
      (operatorSageLatentSystem (A := A)).operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap
        (operatorSageLatentSystem (A := A))))
  letI : CompactSpace (OperatorObservationalQuotient
      (operatorSageLatentSystem (A := A))) :=
    (operatorObservationQuotientRangeHomeomorph
      (operatorSageLatentSystem (A := A))).symm.compactSpace
  letI : T2Space (OperatorObservationalQuotient
      (operatorSageLatentSystem (A := A))) :=
    (operatorObservationQuotientRangeHomeomorph
      (operatorSageLatentSystem (A := A))).symm.t2Space
  letI : T2Space (ChiralOperatorQuotientTensor3 A) := by
    infer_instance
  letI : CompactSpace (ChiralOperatorObservationRange A) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap
        (operatorSageLatentSystem (A := A))))
  letI : CompactSpace (ChiralOperatorObservationRangeTensor3 A) := by
    infer_instance
  let e := operatorObservationQuotientRangeHomeomorph
    (operatorSageLatentSystem (A := A))
  change CompHaus.of (ChiralOperatorQuotientTensor3 A) ⟶
    CompHaus.of (ChiralOperatorObservationRangeTensor3 A)
  exact ⟨TopCat.ofHom
    { toFun := fun p => (e p.1, e p.2.1, e p.2.2)
      continuous_toFun := by
        exact (e.continuous_toFun.comp continuous_fst).prodMk
          ((e.continuous_toFun.comp (continuous_fst.comp continuous_snd)).prodMk
            (e.continuous_toFun.comp (continuous_snd.comp continuous_snd))) }⟩

theorem chiralOperatorQuotientTensor3ObservationRangeHom_R12_naturality :
    chiralOperatorQuotientTensor3ObservationRangeHom (A := A) ≫
        (chiralOperatorObservationRangeTensorR12CompHausIso (A := A)).hom =
      (chiralOperatorQuotientTensor3CompHausR12Iso (A := A)).hom ≫
        chiralOperatorQuotientTensor3ObservationRangeHom (A := A) := by
  apply ConcreteCategory.hom_ext
  intro p
  change ChiralOperatorQuotientTensor3 A at p
  let e := operatorObservationQuotientRangeHomeomorph
    (operatorSageLatentSystem (A := A))
  change (e p.2.1, e p.1, e p.2.2) =
    (e p.2.1, e p.1, e p.2.2)
  rfl

theorem chiralOperatorQuotientTensor3ObservationRangeHom_R23_naturality :
    chiralOperatorQuotientTensor3ObservationRangeHom (A := A) ≫
        (chiralOperatorObservationRangeTensorR23CompHausIso (A := A)).hom =
      (chiralOperatorQuotientTensor3CompHausR23Iso (A := A)).hom ≫
        chiralOperatorQuotientTensor3ObservationRangeHom (A := A) := by
  apply ConcreteCategory.hom_ext
  intro p
  change ChiralOperatorQuotientTensor3 A at p
  let e := operatorObservationQuotientRangeHomeomorph
    (operatorSageLatentSystem (A := A))
  change (e p.1, e p.2.2, e p.2.1) =
    (e p.1, e p.2.2, e p.2.1)
  rfl

theorem chiralOperatorObservationRangeTensorR12Homeomorph_yang_baxter :
    (chiralOperatorObservationRangeTensorR12Homeomorph (A := A)).trans
        ((chiralOperatorObservationRangeTensorR23Homeomorph (A := A)).trans
          (chiralOperatorObservationRangeTensorR12Homeomorph (A := A))) =
      (chiralOperatorObservationRangeTensorR23Homeomorph (A := A)).trans
        ((chiralOperatorObservationRangeTensorR12Homeomorph (A := A)).trans
          (chiralOperatorObservationRangeTensorR23Homeomorph (A := A))) := by
  apply Homeomorph.ext
  intro p
  rfl

theorem chiralOperatorObservationRangeTensorR12CompHausIso_yang_baxter :
    (chiralOperatorObservationRangeTensorR12CompHausIso (A := A)).hom ≫
        (chiralOperatorObservationRangeTensorR23CompHausIso (A := A)).hom ≫
        (chiralOperatorObservationRangeTensorR12CompHausIso (A := A)).hom =
      (chiralOperatorObservationRangeTensorR23CompHausIso (A := A)).hom ≫
        (chiralOperatorObservationRangeTensorR12CompHausIso (A := A)).hom ≫
        (chiralOperatorObservationRangeTensorR23CompHausIso (A := A)).hom := by
  apply (compHausToTop).map_injective
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change ChiralOperatorObservationRangeTensor3 A at p
  simpa only [Functor.map_comp, TopCat.comp_app] using
    congrArg (fun e => e p)
      (chiralOperatorObservationRangeTensorR12Homeomorph_yang_baxter (A := A))

theorem chiralOperatorObservationRangeTensorR12CompHausIso_quadratic :
    (chiralOperatorObservationRangeTensorR12CompHausIso (A := A)).hom ≫
        (chiralOperatorObservationRangeTensorR12CompHausIso (A := A)).hom =
      𝟙 _ := by
  apply (compHausToTop).map_injective
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change ChiralOperatorObservationRangeTensor3 A at p
  change chiralOperatorObservationRangeTensorR12
      (chiralOperatorObservationRangeTensorR12 p) = p
  rfl

theorem chiralOperatorObservationRangeTensorR23CompHausIso_quadratic :
    (chiralOperatorObservationRangeTensorR23CompHausIso (A := A)).hom ≫
        (chiralOperatorObservationRangeTensorR23CompHausIso (A := A)).hom =
      𝟙 _ := by
  apply (compHausToTop).map_injective
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change ChiralOperatorObservationRangeTensor3 A at p
  change chiralOperatorObservationRangeTensorR23
      (chiralOperatorObservationRangeTensorR23 p) = p
  rfl

end
end InfoGeometry.Topology
