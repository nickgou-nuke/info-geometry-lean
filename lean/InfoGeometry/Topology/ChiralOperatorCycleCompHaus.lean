import InfoGeometry.Topology.ChiralOperatorBraidLatentFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ChiralOperatorLatentQuotientTransport
import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationQuotientCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff order-three colour action

The verified cyclic colour action is packaged on the observational quotient
and on its compact observation range.  The readout homeomorphism intertwines
the two actions, so the order-three law is preserved by the native quotient
transport.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompactSpace A]

noncomputable def chiralOperatorCycleQuotientCompHausHom :
    operatorObservationQuotientCompHaus
        (operatorSageLatentSystem (A := A)) ⟶
      operatorObservationQuotientCompHaus
        (operatorSageLatentSystem (A := A)) := by
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
  change CompHaus.of (ChiralOperatorObservationalQuotient A) ⟶
    CompHaus.of (ChiralOperatorObservationalQuotient A)
  exact ⟨TopCat.ofHom
    { toFun := chiralOperatorCycleQuotientMap
      continuous_toFun := continuous_chiralOperatorCycleQuotientMap }⟩

@[simp] theorem chiralOperatorCycleQuotientCompHausHom_apply
    (q : ChiralOperatorObservationalQuotient A) :
    chiralOperatorCycleQuotientCompHausHom (A := A) q =
      chiralOperatorCycleQuotientMap q := by
  rfl

theorem chiralOperatorCycleQuotientCompHausHom_cube :
    chiralOperatorCycleQuotientCompHausHom (A := A) ≫
        chiralOperatorCycleQuotientCompHausHom (A := A) ≫
          chiralOperatorCycleQuotientCompHausHom (A := A) =
      𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro q
  change chiralOperatorCycleQuotientMap
      (chiralOperatorCycleQuotientMap
        (chiralOperatorCycleQuotientMap q)) = q
  exact chiralOperatorCycleQuotientMap_three q

theorem chiralOperatorCycleQuotientCompHausHom_isIso :
    IsIso (chiralOperatorCycleQuotientCompHausHom (A := A)) := by
  refine IsIso.mk ⟨
    chiralOperatorCycleQuotientCompHausHom (A := A) ≫
      chiralOperatorCycleQuotientCompHausHom (A := A), ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro q
    change chiralOperatorCycleQuotientMap
        (chiralOperatorCycleQuotientMap
          (chiralOperatorCycleQuotientMap q)) = q
    exact chiralOperatorCycleQuotientMap_three q
  · apply ConcreteCategory.hom_ext
    intro q
    change chiralOperatorCycleQuotientMap
        (chiralOperatorCycleQuotientMap
          (chiralOperatorCycleQuotientMap q)) = q
    exact chiralOperatorCycleQuotientMap_three q

noncomputable def chiralOperatorCycleRangeMap :
    ChiralOperatorObservationalQuotient A →
      ChiralOperatorObservationalQuotient A :=
  chiralOperatorCycleQuotientMap

def chiralOperatorCycleObservationRangeValue
    (q : Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap) :
    OperatorSageFeatureSpace A :=
  fun i => q.1 (operatorSageFeatureCycle i)

theorem chiralOperatorCycleObservationRangeValue_mem
    (q : Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap) :
    chiralOperatorCycleObservationRangeValue q ∈
      Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap := by
  let X := Classical.choose q.2
  have hX : operatorSageObservationMap X = q.1 :=
    Classical.choose_spec q.2
  refine ⟨chiralOperatorCycle X, ?_⟩
  funext i
  change operatorSageObservationMap (chiralOperatorCycle X) i =
    q.1 (operatorSageFeatureCycle i)
  rw [operatorSageObservation_cycle_intertwines X i, ← hX]

def chiralOperatorCycleObservationRangeMap :
    Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap →
      Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap :=
  fun q => ⟨chiralOperatorCycleObservationRangeValue q,
    chiralOperatorCycleObservationRangeValue_mem q⟩

theorem continuous_chiralOperatorCycleObservationRangeMap :
    Continuous (chiralOperatorCycleObservationRangeMap (A := A)) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi (fun i =>
    (continuous_apply (operatorSageFeatureCycle i)).comp
      continuous_subtype_val)

noncomputable def chiralOperatorCycleObservationRangeCompHausHom :
    operatorObservationRangeCompHaus
        (operatorSageLatentSystem (A := A)) ⟶
      operatorObservationRangeCompHaus
        (operatorSageLatentSystem (A := A)) := by
  letI : CompactSpace (Set.range
      (operatorSageLatentSystem (A := A)).operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap
        (operatorSageLatentSystem (A := A))))
  change CompHaus.of (Set.range
      (operatorSageLatentSystem (A := A)).operatorObservationMap) ⟶
    CompHaus.of (Set.range
      (operatorSageLatentSystem (A := A)).operatorObservationMap)
  exact ⟨TopCat.ofHom
    { toFun := chiralOperatorCycleObservationRangeMap
      continuous_toFun := continuous_chiralOperatorCycleObservationRangeMap }⟩

@[simp] theorem chiralOperatorCycleObservationRangeCompHausHom_apply
    (q : Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap) :
    chiralOperatorCycleObservationRangeCompHausHom (A := A) q =
      chiralOperatorCycleObservationRangeMap q := by
  rfl

theorem chiralOperatorCycleObservationRangeCompHausHom_cube :
    chiralOperatorCycleObservationRangeCompHausHom (A := A) ≫
        chiralOperatorCycleObservationRangeCompHausHom (A := A) ≫
          chiralOperatorCycleObservationRangeCompHausHom (A := A) =
      𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro q
  change Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap at q
  change chiralOperatorCycleObservationRangeMap
      (chiralOperatorCycleObservationRangeMap
        (chiralOperatorCycleObservationRangeMap q)) = q
  apply Subtype.ext
  change (fun i => q.1 (operatorSageFeatureCycle
      (operatorSageFeatureCycle (operatorSageFeatureCycle i)))) = q.1
  funext i
  fin_cases i <;> rfl

theorem chiralOperatorCycleObservationRangeCompHausHom_isIso :
    IsIso (chiralOperatorCycleObservationRangeCompHausHom (A := A)) := by
  refine IsIso.mk ⟨
    chiralOperatorCycleObservationRangeCompHausHom (A := A) ≫
      chiralOperatorCycleObservationRangeCompHausHom (A := A), ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro q
    change Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap at q
    change chiralOperatorCycleObservationRangeMap
        (chiralOperatorCycleObservationRangeMap
          (chiralOperatorCycleObservationRangeMap q)) = q
    apply Subtype.ext
    change (fun i => q.1 (operatorSageFeatureCycle
        (operatorSageFeatureCycle (operatorSageFeatureCycle i)))) = q.1
    funext i
    fin_cases i <;> rfl
  · apply ConcreteCategory.hom_ext
    intro q
    change Set.range (operatorSageLatentSystem (A := A)).operatorObservationMap at q
    change chiralOperatorCycleObservationRangeMap
        (chiralOperatorCycleObservationRangeMap
          (chiralOperatorCycleObservationRangeMap q)) = q
    apply Subtype.ext
    change (fun i => q.1 (operatorSageFeatureCycle
        (operatorSageFeatureCycle (operatorSageFeatureCycle i)))) = q.1
    funext i
    fin_cases i <;> rfl

theorem chiralOperatorCycleObservationRangeCompHausHom_natural :
    (operatorObservationQuotientCompHausIso
        (operatorSageLatentSystem (A := A))).hom ≫
        chiralOperatorCycleObservationRangeCompHausHom (A := A) =
      chiralOperatorCycleQuotientCompHausHom (A := A) ≫
        (operatorObservationQuotientCompHausIso
          (operatorSageLatentSystem (A := A))).hom := by
  apply ConcreteCategory.hom_ext
  intro q
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  simp only [operatorObservationQuotientCompHausIso_hom_apply,
    chiralOperatorCycleObservationRangeCompHausHom_apply,
    chiralOperatorCycleQuotientCompHausHom_apply]
  apply Subtype.ext
  change (fun i =>
      (operatorObservationQuotientRangeMap
        (operatorSageLatentSystem (A := A)) q).1
        (operatorSageFeatureCycle i)) =
    (operatorObservationQuotientRangeMap
      (operatorSageLatentSystem (A := A))
      (chiralOperatorCycleQuotientMap q)).1
  rw [operatorObservationQuotientRangeMap_val,
    operatorObservationQuotientRangeMap_val]
  exact (chiralOperatorCycleQuotientReadout_intertwines
    (A := A) q).symm

end
end InfoGeometry.Topology
