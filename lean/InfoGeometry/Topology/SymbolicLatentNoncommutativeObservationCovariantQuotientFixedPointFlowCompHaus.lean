import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantQuotientFixedPointsCompHaus

/-!
# Restricted covariant flows on fixed-point quotients

The fixed-point equalizer of a time `t` is preserved by every other time
slice.  This owner packages that restriction as a `CompHaus` flow with the
same identity, composition, and inverse-time laws as the ambient quotient.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def operatorObservationQuotientCovariantFixedPointFlowHom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (fixedTime s : ℝ) :
    operatorObservationQuotientCovariantFixedPointCompHaus Φ fixedTime ⟶
      operatorObservationQuotientCovariantFixedPointCompHaus Φ fixedTime := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  letI : CompactSpace (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.compactSpace
  letI : T2Space (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.t2Space
  letI : CompactSpace
      (operatorObservationQuotientCovariantFixedPointSet Φ fixedTime) :=
    isCompact_iff_compactSpace.mp
      (isClosed_operatorObservationQuotientCovariantFixedPointSet Φ fixedTime).isCompact
  change CompHaus.of
      (operatorObservationQuotientCovariantFixedPointSet Φ fixedTime) ⟶
    CompHaus.of
      (operatorObservationQuotientCovariantFixedPointSet Φ fixedTime)
  exact ⟨TopCat.ofHom
    { toFun := fun q =>
        ⟨descendedCovariantOperatorObservationFlow Φ s q.1,
          operatorObservationQuotientCovariantFixedPointSet_flow_invariant
            Φ fixedTime s q.1 q.2⟩
      continuous_toFun := by
        exact (continuous_descendedCovariantOperatorObservationFlow Φ s).comp
          continuous_subtype_val |>.subtype_mk _ }⟩

@[simp] theorem operatorObservationQuotientCovariantFixedPointFlowHom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (fixedTime s : ℝ)
    (q : operatorObservationQuotientCovariantFixedPointSet Φ fixedTime) :
    operatorObservationQuotientCovariantFixedPointFlowHom Φ fixedTime s q =
      ⟨descendedCovariantOperatorObservationFlow Φ s q.1,
        operatorObservationQuotientCovariantFixedPointSet_flow_invariant
          Φ fixedTime s q.1 q.2⟩ := by
  rfl

theorem operatorObservationQuotientCovariantFixedPointFlowHom_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (fixedTime : ℝ) :
    operatorObservationQuotientCovariantFixedPointFlowHom Φ fixedTime 0 =
      𝟙 (operatorObservationQuotientCovariantFixedPointCompHaus Φ fixedTime) := by
  apply ConcreteCategory.hom_ext
  intro q
  apply Subtype.ext
  exact descendedCovariantOperatorObservationFlow_zero Φ q.1

theorem operatorObservationQuotientCovariantFixedPointFlowHom_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (fixedTime s r : ℝ) :
    operatorObservationQuotientCovariantFixedPointFlowHom Φ fixedTime (s + r) =
      operatorObservationQuotientCovariantFixedPointFlowHom Φ fixedTime r ≫
        operatorObservationQuotientCovariantFixedPointFlowHom Φ fixedTime s := by
  apply ConcreteCategory.hom_ext
  intro q
  apply Subtype.ext
  change descendedCovariantOperatorObservationFlow Φ (s + r) q.1 =
    descendedCovariantOperatorObservationFlow Φ s
      (descendedCovariantOperatorObservationFlow Φ r q.1)
  exact descendedCovariantOperatorObservationFlow_add Φ s r q.1

theorem operatorObservationQuotientCovariantFixedPointFlowHom_isIso
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (fixedTime s : ℝ) :
    CategoryTheory.IsIso
      (operatorObservationQuotientCovariantFixedPointFlowHom Φ fixedTime s) := by
  refine CategoryTheory.IsIso.mk
    ⟨operatorObservationQuotientCovariantFixedPointFlowHom Φ fixedTime (-s), ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    calc
      descendedCovariantOperatorObservationFlow Φ (-s)
          (descendedCovariantOperatorObservationFlow Φ s q.1) =
          descendedCovariantOperatorObservationFlow Φ (-s + s) q.1 := by
        exact (descendedCovariantOperatorObservationFlow_add Φ (-s) s q.1).symm
      _ = q.1 := by
        rw [neg_add_cancel]
        exact descendedCovariantOperatorObservationFlow_zero Φ q.1
  · apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    calc
      descendedCovariantOperatorObservationFlow Φ s
          (descendedCovariantOperatorObservationFlow Φ (-s) q.1) =
          descendedCovariantOperatorObservationFlow Φ (s + -s) q.1 := by
        exact (descendedCovariantOperatorObservationFlow_add Φ s (-s) q.1).symm
      _ = q.1 := by
        rw [add_neg_cancel]
        exact descendedCovariantOperatorObservationFlow_zero Φ q.1

end InfoGeometry.Topology
