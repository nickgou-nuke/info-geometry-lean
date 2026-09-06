import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantCompHausRangeAction

/-!
# Joint continuity of the covariant action on the operator-observation range

The covariant-flow structure supplies the algebraic time law but deliberately
does not assert continuity of an arbitrary `StarAlgEquiv` family.  This owner
accepts that missing analytic datum explicitly and transports it to the
compact observation range.
-/

noncomputable section

namespace InfoGeometry.Topology

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def operatorObservationRangeCovariantFlowJointAction
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (h_action_cont :
      Continuous (fun p : ℝ × A => Φ.operatorAction p.1 p.2)) :
    ℝ × Set.range S.operatorObservationMap →
      Set.range S.operatorObservationMap :=
  fun p =>
    ⟨fun i => Φ.operatorAction p.1 (p.2.1 i), by
      rcases p.2.2 with ⟨x, hx⟩
      refine ⟨Φ.act p.1 x, ?_⟩
      funext i
      change (S.observable i).eval (Φ.act p.1 x) = _
      rw [Φ.observation_covariant]
      have hi := congrFun hx i
      change (S.observable i).eval x = p.2.1 i at hi
      rw [hi]⟩

@[simp] theorem operatorObservationRangeCovariantFlowJointAction_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (h_action_cont :
      Continuous (fun p : ℝ × A => Φ.operatorAction p.1 p.2))
    (p : ℝ × Set.range S.operatorObservationMap) :
    operatorObservationRangeCovariantFlowJointAction Φ h_action_cont p =
      ⟨fun i => Φ.operatorAction p.1 (p.2.1 i), by
        rcases p.2.2 with ⟨x, hx⟩
        refine ⟨Φ.act p.1 x, ?_⟩
        funext i
        change (S.observable i).eval (Φ.act p.1 x) = _
        rw [Φ.observation_covariant]
        have hi := congrFun hx i
        change (S.observable i).eval x = p.2.1 i at hi
        rw [hi]⟩ := by
  rfl

theorem continuous_operatorObservationRangeCovariantFlowJointAction
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (h_action_cont :
      Continuous (fun p : ℝ × A => Φ.operatorAction p.1 p.2)) :
    Continuous (operatorObservationRangeCovariantFlowJointAction Φ h_action_cont) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i =>
    h_action_cont.comp
      (continuous_fst.prodMk
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))))

theorem operatorObservationRangeCovariantFlowJointAction_slice
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (h_action_cont :
      Continuous (fun p : ℝ × A => Φ.operatorAction p.1 p.2))
    (t : ℝ) (y : Set.range S.operatorObservationMap) :
    operatorObservationRangeCovariantFlowJointAction Φ h_action_cont (t, y) =
      operatorObservationRangeCompHausCovariantFlowHom Φ t
        (h_action_cont.comp (continuous_const.prodMk continuous_id)) y := by
  rfl

end InfoGeometry.Topology

end
