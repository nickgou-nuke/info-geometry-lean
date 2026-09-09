import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantQuotientCompHausFlow

/-!
# Fixed points of covariant operator-observation quotient flows

For every time `t`, the fixed-point locus of the descended covariant flow is
an equalizer.  On a compact latent carrier it is therefore a compact
Hausdorff subtype.  The result is purely topological and does not identify
the `StarAlgEquiv` action with a topological action on the range.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

def operatorObservationQuotientCovariantFixedPointSet
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    Set (OperatorObservationalQuotient S) :=
  {q | descendedCovariantOperatorObservationFlow Φ t q = q}

theorem isClosed_operatorObservationQuotientCovariantFixedPointSet
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    IsClosed (operatorObservationQuotientCovariantFixedPointSet Φ t) := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  letI : CompactSpace (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.compactSpace
  letI : T2Space (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.t2Space
  exact isClosed_eq
    (continuous_descendedCovariantOperatorObservationFlow Φ t)
    continuous_id

noncomputable def operatorObservationQuotientCovariantFixedPointCompHaus
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) : CompHaus := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  letI : CompactSpace (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.compactSpace
  letI : T2Space (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.t2Space
  letI : CompactSpace
      (operatorObservationQuotientCovariantFixedPointSet Φ t) :=
    isCompact_iff_compactSpace.mp
      (isClosed_operatorObservationQuotientCovariantFixedPointSet Φ t).isCompact
  exact CompHaus.of
    (operatorObservationQuotientCovariantFixedPointSet Φ t)

noncomputable def operatorObservationQuotientCovariantFixedPointInclusion
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    operatorObservationQuotientCovariantFixedPointCompHaus Φ t ⟶
      operatorObservationQuotientCompHaus S := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  letI : CompactSpace (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.compactSpace
  letI : T2Space (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.t2Space
  letI : CompactSpace
      (operatorObservationQuotientCovariantFixedPointSet Φ t) :=
    isCompact_iff_compactSpace.mp
      (isClosed_operatorObservationQuotientCovariantFixedPointSet Φ t).isCompact
  change CompHaus.of
      (operatorObservationQuotientCovariantFixedPointSet Φ t) ⟶
    CompHaus.of (OperatorObservationalQuotient S)
  exact ⟨TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }⟩

@[simp] theorem operatorObservationQuotientCovariantFixedPointInclusion_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (q : operatorObservationQuotientCovariantFixedPointSet Φ t) :
    operatorObservationQuotientCovariantFixedPointInclusion Φ t q = q.1 :=
  rfl

theorem operatorObservationQuotientCovariantFixedPointSet_flow_invariant
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t s : ℝ)
    (q : OperatorObservationalQuotient S)
    (hq : q ∈ operatorObservationQuotientCovariantFixedPointSet Φ t) :
    descendedCovariantOperatorObservationFlow Φ s q ∈
      operatorObservationQuotientCovariantFixedPointSet Φ t := by
  change descendedCovariantOperatorObservationFlow Φ t
      (descendedCovariantOperatorObservationFlow Φ s q) =
    descendedCovariantOperatorObservationFlow Φ s q
  calc
    descendedCovariantOperatorObservationFlow Φ t
        (descendedCovariantOperatorObservationFlow Φ s q) =
        descendedCovariantOperatorObservationFlow Φ (t + s) q := by
      exact (descendedCovariantOperatorObservationFlow_add Φ t s q).symm
    _ = descendedCovariantOperatorObservationFlow Φ (s + t) q := by
      rw [add_comm]
    _ = descendedCovariantOperatorObservationFlow Φ s
        (descendedCovariantOperatorObservationFlow Φ t q) := by
      exact descendedCovariantOperatorObservationFlow_add Φ s t q
    _ = descendedCovariantOperatorObservationFlow Φ s q := by
      rw [hq]

end InfoGeometry.Topology
