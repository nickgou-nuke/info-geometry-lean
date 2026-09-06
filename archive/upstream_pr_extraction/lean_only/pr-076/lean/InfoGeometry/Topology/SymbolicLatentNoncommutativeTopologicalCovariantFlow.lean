import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantCompHausRangeJointContinuity

/-!
# Topological packaging of a covariant noncommutative symbolic-latent flow

`NoncommutativeObservableCovariantFlow` owns the algebraic time action and
its quotient laws.  This owner adds only the missing joint continuity of the
operator action, then derives the corresponding continuous action on the
compact observation range.
-/

noncomputable section

namespace InfoGeometry.Topology

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

structure NoncommutativeObservableTopologicalCovariantFlow
    (S : NoncommutativeObservableSystem X A ι) where
  base : NoncommutativeObservableCovariantFlow S
  operatorAction_continuous :
    Continuous (fun p : ℝ × A => base.operatorAction p.1 p.2)

abbrev NoncommutativeObservableTopologicalCovariantFlow.baseFlow
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    NoncommutativeObservableCovariantFlow S :=
  F.base

def topologicalCovariantRangeAction
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    ℝ × Set.range S.operatorObservationMap →
      Set.range S.operatorObservationMap :=
  operatorObservationRangeCovariantFlowJointAction F.base
    F.operatorAction_continuous

theorem continuous_topologicalCovariantRangeAction
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    Continuous (topologicalCovariantRangeAction F) :=
  continuous_operatorObservationRangeCovariantFlowJointAction F.base
    F.operatorAction_continuous

@[simp] theorem topologicalCovariantRangeAction_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (y : Set.range S.operatorObservationMap) :
    topologicalCovariantRangeAction F (t, y) =
      ⟨fun i => F.base.operatorAction t (y.1 i), by
        rcases y.2 with ⟨x, hx⟩
        refine ⟨F.base.act t x, ?_⟩
        funext i
        change (S.observable i).eval (F.base.act t x) = _
        rw [F.base.observation_covariant]
        have hi := congrFun hx i
        change (S.observable i).eval x = y.1 i at hi
        rw [hi]⟩ := by
  rfl

theorem topologicalCovariantRangeAction_zero
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (y : Set.range S.operatorObservationMap) :
    topologicalCovariantRangeAction F (0, y) = y := by
  apply Subtype.ext
  funext i
  change F.base.operatorAction 0 (y.1 i) = y.1 i
  exact F.base.operatorAction_zero _

theorem topologicalCovariantRangeAction_add
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (s t : ℝ) (y : Set.range S.operatorObservationMap) :
    topologicalCovariantRangeAction F (s + t, y) =
      topologicalCovariantRangeAction F
        (s, topologicalCovariantRangeAction F (t, y)) := by
  apply Subtype.ext
  funext i
  change F.base.operatorAction (s + t) (y.1 i) =
    F.base.operatorAction s (F.base.operatorAction t (y.1 i))
  exact F.base.operatorAction_add s t _

end InfoGeometry.Topology

end
