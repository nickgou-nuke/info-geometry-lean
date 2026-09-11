import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantCompHausRangeActionLaws
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Fixed points of the covariant action on the operator-observation range

This is the range-side analogue of the quotient fixed-point owner.  The
continuity of the `StarAlgEquiv` slice is an explicit parameter, so the
construction does not smuggle a topological structure into the algebraic
covariant-flow data.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

def operatorObservationRangeCovariantFixedPointSet
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t)) :
    Set (Set.range S.operatorObservationMap) :=
  {y | operatorObservationRangeCompHausCovariantFlowHom Φ t h_t y = y}

theorem isClosed_operatorObservationRangeCovariantFixedPointSet
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t)) :
    IsClosed (operatorObservationRangeCovariantFixedPointSet Φ t h_t) := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  exact isClosed_eq
    (by
      apply Continuous.subtype_mk
      exact continuous_pi (fun i =>
        h_t.comp ((continuous_apply i).comp continuous_subtype_val)))
    continuous_id

noncomputable def operatorObservationRangeCovariantFixedPointCompHaus
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t)) : CompHaus := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  letI : CompactSpace
      (operatorObservationRangeCovariantFixedPointSet Φ t h_t) :=
    isCompact_iff_compactSpace.mp
      (isClosed_operatorObservationRangeCovariantFixedPointSet Φ t h_t).isCompact
  exact CompHaus.of
    (operatorObservationRangeCovariantFixedPointSet Φ t h_t)

noncomputable def operatorObservationRangeCovariantFixedPointInclusion
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t)) :
    operatorObservationRangeCovariantFixedPointCompHaus Φ t h_t ⟶
      operatorObservationRangeCompHaus S := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  letI : CompactSpace
      (operatorObservationRangeCovariantFixedPointSet Φ t h_t) :=
    isCompact_iff_compactSpace.mp
      (isClosed_operatorObservationRangeCovariantFixedPointSet Φ t h_t).isCompact
  change CompHaus.of
      (operatorObservationRangeCovariantFixedPointSet Φ t h_t) ⟶
    CompHaus.of (Set.range S.operatorObservationMap)
  exact ⟨TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }⟩

@[simp] theorem operatorObservationRangeCovariantFixedPointInclusion_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t))
    (y : operatorObservationRangeCovariantFixedPointSet Φ t h_t) :
    operatorObservationRangeCovariantFixedPointInclusion Φ t h_t y = y.1 :=
  rfl

theorem operatorObservationRangeCovariantFixedPointSet_flow_invariant
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t s : ℝ)
    (h_t : Continuous (Φ.operatorAction t))
    (h_s : Continuous (Φ.operatorAction s))
    (y : Set.range S.operatorObservationMap)
    (hy : y ∈ operatorObservationRangeCovariantFixedPointSet Φ t h_t) :
    operatorObservationRangeCompHausCovariantFlowHom Φ s h_s y ∈
      operatorObservationRangeCovariantFixedPointSet Φ t h_t := by
  change operatorObservationRangeCompHausCovariantFlowHom Φ t h_t
      (operatorObservationRangeCompHausCovariantFlowHom Φ s h_s y) =
    operatorObservationRangeCompHausCovariantFlowHom Φ s h_s y
  apply Subtype.ext
  funext i
  change Φ.operatorAction t (Φ.operatorAction s (y.1 i)) =
    Φ.operatorAction s (y.1 i)
  calc
    Φ.operatorAction t (Φ.operatorAction s (y.1 i)) =
        Φ.operatorAction (t + s) (y.1 i) :=
      (Φ.operatorAction_add t s _).symm
    _ = Φ.operatorAction (s + t) (y.1 i) := by rw [add_comm]
    _ = Φ.operatorAction s (Φ.operatorAction t (y.1 i)) :=
      Φ.operatorAction_add s t _
    _ = Φ.operatorAction s (y.1 i) := by
      have hi := congrArg Subtype.val hy
      have hii := congrFun hi i
      change Φ.operatorAction t (y.1 i) = y.1 i at hii
      rw [hii]

end InfoGeometry.Topology
