import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantCompHausRangeAction

/-!
# Flow laws for the compact operator-observation range action

The range action is defined with an explicit continuity hypothesis because an
arbitrary `StarAlgEquiv` is not assumed continuous by the observable-system
API.  Its algebraic flow laws, however, follow directly from the covariant
flow's zero and addition laws.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

theorem operatorObservationRangeCompHausCovariantFlowHom_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (h_action_cont : Continuous (Φ.operatorAction 0)) :
    operatorObservationRangeCompHausCovariantFlowHom Φ 0 h_action_cont =
      𝟙 (operatorObservationRangeCompHaus S) := by
  apply ConcreteCategory.hom_ext
  intro y
  apply Subtype.ext
  funext i
  change Φ.operatorAction 0 (y.1 i) = y.1 i
  exact Φ.operatorAction_zero _

theorem operatorObservationRangeCompHausCovariantFlowHom_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (s t : ℝ)
    (h_st : Continuous (Φ.operatorAction (s + t)))
    (h_t : Continuous (Φ.operatorAction t))
    (h_s : Continuous (Φ.operatorAction s)) :
    operatorObservationRangeCompHausCovariantFlowHom Φ (s + t) h_st =
      operatorObservationRangeCompHausCovariantFlowHom Φ t h_t ≫
        operatorObservationRangeCompHausCovariantFlowHom Φ s h_s := by
  apply ConcreteCategory.hom_ext
  intro y
  apply Subtype.ext
  funext i
  change Φ.operatorAction (s + t) (y.1 i) =
    Φ.operatorAction s (Φ.operatorAction t (y.1 i))
  exact Φ.operatorAction_add s t _

theorem operatorObservationRangeCompHausCovariantFlowHom_isIso
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t))
    (h_neg_t : Continuous (Φ.operatorAction (-t))) :
    IsIso (operatorObservationRangeCompHausCovariantFlowHom Φ t h_t) := by
  refine IsIso.mk
    ⟨operatorObservationRangeCompHausCovariantFlowHom Φ (-t) h_neg_t, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    funext i
    change Φ.operatorAction (-t) (Φ.operatorAction t (y.1 i)) = y.1 i
    calc
      Φ.operatorAction (-t) (Φ.operatorAction t (y.1 i)) =
          Φ.operatorAction (-t + t) (y.1 i) :=
        (Φ.operatorAction_add (-t) t _).symm
      _ = y.1 i := by
        rw [neg_add_cancel]
        exact Φ.operatorAction_zero _
  · apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    funext i
    change Φ.operatorAction t (Φ.operatorAction (-t) (y.1 i)) = y.1 i
    calc
      Φ.operatorAction t (Φ.operatorAction (-t) (y.1 i)) =
          Φ.operatorAction (t + -t) (y.1 i) :=
        (Φ.operatorAction_add t (-t) _).symm
      _ = y.1 i := by
        rw [add_neg_cancel]
        exact Φ.operatorAction_zero _

end InfoGeometry.Topology

end
