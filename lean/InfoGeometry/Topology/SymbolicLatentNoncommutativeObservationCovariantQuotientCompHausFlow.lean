import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationQuotientCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentNoncommutativeCovariantFlowTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Covariant flows on compact operator-valued observational quotients

The quotient flow is already descended at the `TopCat` level.  This owner
adds the compact-Hausdorff packaging supplied by the operator-valued readout
range, while keeping the `StarAlgEquiv` action entirely in the observation
target.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def operatorObservationQuotientCompHausCovariantFlowHom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    operatorObservationQuotientCompHaus S ⟶
      operatorObservationQuotientCompHaus S := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  letI : CompactSpace (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.compactSpace
  letI : T2Space (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.t2Space
  change CompHaus.of (OperatorObservationalQuotient S) ⟶
    CompHaus.of (OperatorObservationalQuotient S)
  exact ⟨TopCat.ofHom
    { toFun := descendedCovariantOperatorObservationFlow Φ t
      continuous_toFun := continuous_descendedCovariantOperatorObservationFlow Φ t }⟩

@[simp] theorem operatorObservationQuotientCompHausCovariantFlowHom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (q : OperatorObservationalQuotient S) :
    operatorObservationQuotientCompHausCovariantFlowHom Φ t q =
      descendedCovariantOperatorObservationFlow Φ t q := by
  rfl

theorem operatorObservationQuotientCompHausCovariantFlowHom_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) :
    operatorObservationQuotientCompHausCovariantFlowHom Φ 0 =
      𝟙 (operatorObservationQuotientCompHaus S) := by
  apply ConcreteCategory.hom_ext
  intro q
  exact descendedCovariantOperatorObservationFlow_zero Φ q

theorem operatorObservationQuotientCompHausCovariantFlowHom_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (s t : ℝ) :
    operatorObservationQuotientCompHausCovariantFlowHom Φ (s + t) =
      operatorObservationQuotientCompHausCovariantFlowHom Φ t ≫
        operatorObservationQuotientCompHausCovariantFlowHom Φ s := by
  apply ConcreteCategory.hom_ext
  intro q
  change descendedCovariantOperatorObservationFlow Φ (s + t) q =
    descendedCovariantOperatorObservationFlow Φ s
      (descendedCovariantOperatorObservationFlow Φ t q)
  exact descendedCovariantOperatorObservationFlow_add Φ s t q

theorem operatorObservationQuotientCompHausCovariantFlowHom_isIso
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    CategoryTheory.IsIso
      (operatorObservationQuotientCompHausCovariantFlowHom Φ t) := by
  refine CategoryTheory.IsIso.mk
    ⟨operatorObservationQuotientCompHausCovariantFlowHom Φ (-t), ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro q
    change descendedCovariantOperatorObservationFlow Φ (-t)
        (descendedCovariantOperatorObservationFlow Φ t q) = q
    calc
      descendedCovariantOperatorObservationFlow Φ (-t)
          (descendedCovariantOperatorObservationFlow Φ t q) =
          descendedCovariantOperatorObservationFlow Φ (-t + t) q := by
        exact (descendedCovariantOperatorObservationFlow_add Φ (-t) t q).symm
      _ = q := by
        rw [neg_add_cancel]
        exact descendedCovariantOperatorObservationFlow_zero Φ q
  · apply ConcreteCategory.hom_ext
    intro q
    change descendedCovariantOperatorObservationFlow Φ t
        (descendedCovariantOperatorObservationFlow Φ (-t) q) = q
    calc
      descendedCovariantOperatorObservationFlow Φ t
          (descendedCovariantOperatorObservationFlow Φ (-t) q) =
          descendedCovariantOperatorObservationFlow Φ (t + -t) q := by
        exact (descendedCovariantOperatorObservationFlow_add Φ t (-t) q).symm
      _ = q := by
        rw [add_neg_cancel]
        exact descendedCovariantOperatorObservationFlow_zero Φ q

end InfoGeometry.Topology
