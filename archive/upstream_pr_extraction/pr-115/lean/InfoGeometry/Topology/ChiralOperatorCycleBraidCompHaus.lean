import InfoGeometry.Topology.ChiralOperatorCycleCompHaus
import InfoGeometry.Topology.ChiralOperatorQuotientBraidCompHaus

/-!
# Cyclic colour symmetry on the compact quotient braid carrier

The diagonal order-three action is applied independently to the three
observational quotient coordinates.  It is external to the quotient
multiplication and commutes with both tensor-leg swaps.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompactSpace A]

def chiralOperatorCycleQuotientTensor3Map :
    ChiralOperatorQuotientTensor3 A → ChiralOperatorQuotientTensor3 A :=
  fun p =>
    (chiralOperatorCycleQuotientMap p.1,
      chiralOperatorCycleQuotientMap p.2.1,
      chiralOperatorCycleQuotientMap p.2.2)

theorem continuous_chiralOperatorCycleQuotientTensor3Map :
    Continuous (chiralOperatorCycleQuotientTensor3Map (A := A)) := by
  exact
    (continuous_chiralOperatorCycleQuotientMap.comp continuous_fst).prodMk
      ((continuous_chiralOperatorCycleQuotientMap.comp
          (continuous_fst.comp continuous_snd)).prodMk
        (continuous_chiralOperatorCycleQuotientMap.comp
          (continuous_snd.comp continuous_snd)))

noncomputable def chiralOperatorCycleQuotientTensor3CompHausHom :
    chiralOperatorQuotientTensor3CompHaus (A := A) ⟶
      chiralOperatorQuotientTensor3CompHaus (A := A) := by
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
  change CompHaus.of (ChiralOperatorQuotientTensor3 A) ⟶
    CompHaus.of (ChiralOperatorQuotientTensor3 A)
  exact ⟨TopCat.ofHom
    { toFun := chiralOperatorCycleQuotientTensor3Map
      continuous_toFun := continuous_chiralOperatorCycleQuotientTensor3Map }⟩

@[simp] theorem chiralOperatorCycleQuotientTensor3CompHausHom_apply
    (p : ChiralOperatorQuotientTensor3 A) :
    chiralOperatorCycleQuotientTensor3CompHausHom (A := A) p =
      chiralOperatorCycleQuotientTensor3Map p := rfl

theorem chiralOperatorCycleQuotientTensor3CompHausHom_cube :
    chiralOperatorCycleQuotientTensor3CompHausHom (A := A) ≫
        chiralOperatorCycleQuotientTensor3CompHausHom (A := A) ≫
          chiralOperatorCycleQuotientTensor3CompHausHom (A := A) =
      𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro p
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  change chiralOperatorCycleQuotientTensor3Map
      (chiralOperatorCycleQuotientTensor3Map
        (chiralOperatorCycleQuotientTensor3Map p)) = p
  rcases p with ⟨p₁, p₂, p₃⟩
  apply Prod.ext
  · exact chiralOperatorCycleQuotientMap_three p₁
  · apply Prod.ext
    · exact chiralOperatorCycleQuotientMap_three p₂
    · exact chiralOperatorCycleQuotientMap_three p₃

theorem chiralOperatorCycleQuotientTensor3CompHausHom_isIso :
    IsIso (chiralOperatorCycleQuotientTensor3CompHausHom (A := A)) := by
  refine IsIso.mk ⟨
    chiralOperatorCycleQuotientTensor3CompHausHom (A := A) ≫
      chiralOperatorCycleQuotientTensor3CompHausHom (A := A), ?_, ?_⟩
  · exact chiralOperatorCycleQuotientTensor3CompHausHom_cube (A := A)
  · exact chiralOperatorCycleQuotientTensor3CompHausHom_cube (A := A)

theorem chiralOperatorCycleQuotientTensor3CompHausHom_R12_commutes :
    chiralOperatorCycleQuotientTensor3CompHausHom (A := A) ≫
        (chiralOperatorQuotientTensor3CompHausR12Iso (A := A)).hom =
      (chiralOperatorQuotientTensor3CompHausR12Iso (A := A)).hom ≫
        chiralOperatorCycleQuotientTensor3CompHausHom (A := A) := by
  apply ConcreteCategory.hom_ext
  intro p
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  change chiralOperatorQuotientTensorR12
      (chiralOperatorCycleQuotientTensor3Map p) =
    chiralOperatorCycleQuotientTensor3Map
      (chiralOperatorQuotientTensorR12 p)
  rfl

theorem chiralOperatorCycleQuotientTensor3CompHausHom_R23_commutes :
    chiralOperatorCycleQuotientTensor3CompHausHom (A := A) ≫
        (chiralOperatorQuotientTensor3CompHausR23Iso (A := A)).hom =
      (chiralOperatorQuotientTensor3CompHausR23Iso (A := A)).hom ≫
        chiralOperatorCycleQuotientTensor3CompHausHom (A := A) := by
  apply ConcreteCategory.hom_ext
  intro p
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  change chiralOperatorQuotientTensorR23
      (chiralOperatorCycleQuotientTensor3Map p) =
    chiralOperatorCycleQuotientTensor3Map
      (chiralOperatorQuotientTensorR23 p)
  rfl

end
end InfoGeometry.Topology
