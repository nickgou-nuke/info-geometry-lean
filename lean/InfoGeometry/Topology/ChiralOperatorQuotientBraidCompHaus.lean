import InfoGeometry.Topology.ChiralOperatorTopologicalBraidCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationQuotientCompHaus

/-!
# Compact-Hausdorff quotient braid action

The quotient braid action is promoted to `CompHaus` only under the explicit
compactness property on the coefficient carrier.  The general topological
action remains in the preceding `TopCat` owner.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompactSpace A]

noncomputable def chiralOperatorQuotientTensor3CompHaus : CompHaus := by
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
  exact CompHaus.of
    (ChiralOperatorQuotientTensor3 A)

noncomputable def chiralOperatorQuotientTensor3CompHausR12Iso :
    chiralOperatorQuotientTensor3CompHaus (A := A) ≅
      chiralOperatorQuotientTensor3CompHaus (A := A) := by
  let e := chiralOperatorQuotientTensorR12Homeomorph (A := A)
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

noncomputable def chiralOperatorQuotientTensor3CompHausR23Iso :
    chiralOperatorQuotientTensor3CompHaus (A := A) ≅
      chiralOperatorQuotientTensor3CompHaus (A := A) := by
  let e := chiralOperatorQuotientTensorR23Homeomorph (A := A)
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

theorem chiralOperatorQuotientTensor3CompHausR12Iso_yang_baxter :
    (chiralOperatorQuotientTensor3CompHausR12Iso (A := A)).hom ≫
        (chiralOperatorQuotientTensor3CompHausR23Iso (A := A)).hom ≫
        (chiralOperatorQuotientTensor3CompHausR12Iso (A := A)).hom =
      (chiralOperatorQuotientTensor3CompHausR23Iso (A := A)).hom ≫
        (chiralOperatorQuotientTensor3CompHausR12Iso (A := A)).hom ≫
        (chiralOperatorQuotientTensor3CompHausR23Iso (A := A)).hom := by
  apply (compHausToTop).map_injective
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change ChiralOperatorQuotientTensor3 A at p
  simpa only [Functor.map_comp, TopCat.comp_app] using
    chiralOperatorQuotientTensorR12_yang_baxter p

theorem chiralOperatorQuotientTensor3CompHausR12Iso_quadratic :
    (chiralOperatorQuotientTensor3CompHausR12Iso (A := A)).hom ≫
        (chiralOperatorQuotientTensor3CompHausR12Iso (A := A)).hom =
      𝟙 _ := by
  apply (compHausToTop).map_injective
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change ChiralOperatorQuotientTensor3 A at p
  simpa only [Functor.map_comp, TopCat.comp_app, TopCat.id_app] using
    chiralOperatorQuotientTensorR12_quadratic p

theorem chiralOperatorQuotientTensor3CompHausR23Iso_quadratic :
    (chiralOperatorQuotientTensor3CompHausR23Iso (A := A)).hom ≫
        (chiralOperatorQuotientTensor3CompHausR23Iso (A := A)).hom =
      𝟙 _ := by
  apply (compHausToTop).map_injective
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change ChiralOperatorQuotientTensor3 A at p
  simpa only [Functor.map_comp, TopCat.comp_app, TopCat.id_app] using
    chiralOperatorQuotientTensorR23_quadratic p

end
end InfoGeometry.Topology
