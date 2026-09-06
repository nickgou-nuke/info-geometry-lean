import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCompHausLocus
import InfoGeometry.Topology.SymbolicLatentNoncommutativeCovariantFlowTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Covariant flows on compact operator-commuting loci

This owner transports a covariant `StarAlgEquiv` action only through the
latent flow.  The algebra-valued observables remain in their existing target;
the compact carrier is the commuting-locus subtype.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def operatorCommutingLocusCompHausCovariantFlowHom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    operatorCommutingLocusCompHaus S ⟶
      operatorCommutingLocusCompHaus S := by
  letI : CompactSpace {x : X // x ∈ operatorCommutingLocus S} :=
    isCompact_iff_compactSpace.mp (isCompact_operatorCommutingLocus S)
  change CompHaus.of {x : X // x ∈ operatorCommutingLocus S} ⟶
    CompHaus.of {x : X // x ∈ operatorCommutingLocus S}
  exact ⟨TopCat.ofHom
    { toFun := fun x =>
        ⟨Φ.act t x.1,
          (operatorCommutingLocus_covariant_iff Φ t x.1).2 x.2⟩
      continuous_toFun := by
        exact (Φ.continuous_act.comp
          (continuous_const.prodMk continuous_subtype_val)).subtype_mk _ }⟩

@[simp] theorem operatorCommutingLocusCompHausCovariantFlowHom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (x : {x : X // x ∈ operatorCommutingLocus S}) :
    operatorCommutingLocusCompHausCovariantFlowHom Φ t x =
      ⟨Φ.act t x.1,
        (operatorCommutingLocus_covariant_iff Φ t x.1).2 x.2⟩ := by
  rfl

theorem operatorCommutingLocusCompHausCovariantFlowHom_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) :
    operatorCommutingLocusCompHausCovariantFlowHom Φ 0 =
      𝟙 (operatorCommutingLocusCompHaus S) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact Φ.act_zero x.1

theorem operatorCommutingLocusCompHausCovariantFlowHom_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (s t : ℝ) :
    operatorCommutingLocusCompHausCovariantFlowHom Φ (s + t) =
      operatorCommutingLocusCompHausCovariantFlowHom Φ t ≫
        operatorCommutingLocusCompHausCovariantFlowHom Φ s := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change Φ.act (s + t) x.1 = Φ.act s (Φ.act t x.1)
  exact Φ.act_add s t x.1

theorem operatorCommutingLocusCompHausCovariantFlowHom_isIso
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    CategoryTheory.IsIso
      (operatorCommutingLocusCompHausCovariantFlowHom Φ t) := by
  refine CategoryTheory.IsIso.mk
    ⟨operatorCommutingLocusCompHausCovariantFlowHom Φ (-t), ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change Φ.act (-t) (Φ.act t x.1) = x.1
    calc
      Φ.act (-t) (Φ.act t x.1) = Φ.act (-t + t) x.1 := by
        exact (Φ.act_add (-t) t x.1).symm
      _ = x.1 := by rw [neg_add_cancel, Φ.act_zero]
  · apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change Φ.act t (Φ.act (-t) x.1) = x.1
    calc
      Φ.act t (Φ.act (-t) x.1) = Φ.act (t + -t) x.1 := by
        exact (Φ.act_add t (-t) x.1).symm
      _ = x.1 := by rw [add_neg_cancel, Φ.act_zero]

end InfoGeometry.Topology

end
