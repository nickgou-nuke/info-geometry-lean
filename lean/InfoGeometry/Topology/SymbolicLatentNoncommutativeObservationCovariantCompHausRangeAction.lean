import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantCompHausReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# The induced `CompHaus` action on the operator-observation range

The covariant flow already transports operator-valued observations by a
`StarAlgEquiv`.  This owner packages the induced action on the compact range
of the observation map and upgrades pointwise covariance to a commutative
square in `CompHaus`.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def operatorObservationRangeCompHausCovariantFlowHom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_action_cont : Continuous (Φ.operatorAction t)) :
    operatorObservationRangeCompHaus S ⟶
      operatorObservationRangeCompHaus S := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  change CompHaus.of (Set.range S.operatorObservationMap) ⟶
    CompHaus.of (Set.range S.operatorObservationMap)
  exact ⟨TopCat.ofHom
    { toFun := fun y =>
        ⟨fun i => Φ.operatorAction t (y.1 i), by
          rcases y.2 with ⟨x, hx⟩
          refine ⟨Φ.act t x, ?_⟩
          funext i
          change (S.observable i).eval (Φ.act t x) = _
          rw [Φ.observation_covariant]
          have hi := congrFun hx i
          change (S.observable i).eval x = y.1 i at hi
          rw [hi]⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_pi (fun i =>
          h_action_cont.comp
            ((continuous_apply i).comp continuous_subtype_val)) }⟩

@[simp] theorem operatorObservationRangeCompHausCovariantFlowHom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_action_cont : Continuous (Φ.operatorAction t))
    (y : Set.range S.operatorObservationMap) :
    operatorObservationRangeCompHausCovariantFlowHom Φ t h_action_cont y =
      ⟨fun i => Φ.operatorAction t (y.1 i), by
        rcases y.2 with ⟨x, hx⟩
        refine ⟨Φ.act t x, ?_⟩
        funext i
        change (S.observable i).eval (Φ.act t x) = _
        rw [Φ.observation_covariant]
        have hi := congrFun hx i
        change (S.observable i).eval x = y.1 i at hi
        rw [hi]⟩ := by
  rfl

theorem operatorObservationQuotientCompHausReadout_covariant_square
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_action_cont : Continuous (Φ.operatorAction t)) :
    operatorObservationQuotientCompHausCovariantFlowHom Φ t ≫
        operatorObservationQuotientCompHausReadoutHom S =
      operatorObservationQuotientCompHausReadoutHom S ≫
        operatorObservationRangeCompHausCovariantFlowHom Φ t h_action_cont := by
  apply ConcreteCategory.hom_ext
  intro q
  apply Subtype.ext
  change
    (operatorObservationQuotientRangeMap S
        (descendedCovariantOperatorObservationFlow Φ t q)).1 =
      fun i => Φ.operatorAction t
        ((operatorObservationQuotientRangeMap S q).1 i)
  rw [operatorObservationQuotientRangeMap_val,
    operatorObservationQuotientRangeMap_val]
  exact operatorObservationQuotientReadout_covariant Φ t q

end InfoGeometry.Topology
