import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCompHausLocus
import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationQuotientFlowTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Flow slices on the compact operator-commuting locus

The profile-preserving noncommutative flow preserves the commuting locus.
This owner packages each time slice as a `CompHaus` morphism on that compact
Hausdorff subtype and transports the zero and additive laws without changing
the operator-valued observation target.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [Fintype ι]

noncomputable def operatorCommutingLocusCompHausFlowHom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ) :
    operatorCommutingLocusCompHaus S ⟶
      operatorCommutingLocusCompHaus S := by
  letI : CompactSpace {x : X // x ∈ operatorCommutingLocus S} :=
    isCompact_iff_compactSpace.mp (isCompact_operatorCommutingLocus S)
  change CompHaus.of {x : X // x ∈ operatorCommutingLocus S} ⟶
    CompHaus.of {x : X // x ∈ operatorCommutingLocus S}
  exact ⟨TopCat.ofHom
    { toFun := fun x =>
        ⟨Φ.act t x.1,
          (operatorCommutingLocus_flow_iff Φ t x.1).2 x.2⟩
      continuous_toFun := by
        exact (Φ.continuous_act.comp
          (continuous_const.prodMk continuous_subtype_val)).subtype_mk _ }⟩

theorem operatorCommutingLocusCompHausFlowHom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ)
    (x : {x : X // x ∈ operatorCommutingLocus S}) :
    operatorCommutingLocusCompHausFlowHom Φ t x =
      ⟨Φ.act t x.1, (operatorCommutingLocus_flow_iff Φ t x.1).2 x.2⟩ := by
  rfl

theorem operatorCommutingLocusCompHausFlowHom_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) :
    operatorCommutingLocusCompHausFlowHom Φ 0 =
      𝟙 (operatorCommutingLocusCompHaus S) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact Φ.act_zero x.1

theorem operatorCommutingLocusCompHausFlowHom_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (s t : ℝ) :
    operatorCommutingLocusCompHausFlowHom Φ (s + t) =
      operatorCommutingLocusCompHausFlowHom Φ s ≫
        operatorCommutingLocusCompHausFlowHom Φ t := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change Φ.act (s + t) x.1 =
    Φ.act t (Φ.act s x.1)
  rw [add_comm s t, Φ.act_add]

end InfoGeometry.Topology

end
