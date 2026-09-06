import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantCompHausRangeHomeomorph
import InfoGeometry.Topology.SymbolicLatentNoncommutativeTopologicalCovariantFlow
import InfoGeometry.Topology.TopologicalCovariantFlowObservationRangeFunctor
import InfoGeometry.Topology.TopologicalCovariantFlowObservationQuotientFunctor

/-!
# The concrete `CompHaus` action package for topological covariant flows

The repository does not yet define a category of covariant-flow systems, so a
literal functor would be an ungrounded interface.  This owner supplies the
concrete categorical action that such a functor would use: every real time
gets a `CompHaus` isomorphism, and the zero, addition, and inverse laws are
proved from the packaged topological covariant flow.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def topologicalCovariantOperatorAction_continuous
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (t : ℝ) :
    Continuous (fun a : A => F.base.operatorAction t a) :=
  F.operatorAction_continuous.comp (continuous_const.prodMk continuous_id)

noncomputable def topologicalCovariantRangeCompHausIso
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (t : ℝ) :
    operatorObservationRangeCompHaus S ≅ operatorObservationRangeCompHaus S :=
  operatorObservationRangeCovariantFlowCompHausIso F.base t
    (topologicalCovariantOperatorAction_continuous F t)
    (topologicalCovariantOperatorAction_continuous F (-t))

/- The joint continuous action on the compact-Hausdorff observation range. -/
noncomputable def topologicalCovariantRangeCompHausContinuousAction
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    C(ℝ × operatorObservationRangeCompHaus S, operatorObservationRangeCompHaus S) :=
  ContinuousMap.mk
    (fun p => topologicalCovariantRangeAction F (p.1, p.2))
    (continuous_topologicalCovariantRangeAction F)

@[simp] theorem topologicalCovariantRangeCompHausContinuousAction_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (y : operatorObservationRangeCompHaus S) :
    topologicalCovariantRangeCompHausContinuousAction F (t, y) =
      topologicalCovariantRangeAction F (t, y) :=
  rfl

theorem topologicalCovariantRangeCompHausContinuousAction_zero
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (y : operatorObservationRangeCompHaus S) :
    topologicalCovariantRangeCompHausContinuousAction F (0, y) = y := by
  exact topologicalCovariantRangeAction_zero F y

theorem topologicalCovariantRangeCompHausContinuousAction_add
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (s t : ℝ) (y : operatorObservationRangeCompHaus S) :
    topologicalCovariantRangeCompHausContinuousAction F (s + t, y) =
      topologicalCovariantRangeCompHausContinuousAction F
        (s, topologicalCovariantRangeCompHausContinuousAction F (t, y)) := by
  exact topologicalCovariantRangeAction_add F s t y

/- The time slice of the joint action as a native continuous map. -/
noncomputable def topologicalCovariantRangeCompHausContinuousTimeSlice
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) :
    C(operatorObservationRangeCompHaus S, operatorObservationRangeCompHaus S) :=
  ContinuousMap.mk
    (fun y => topologicalCovariantRangeAction F (t, y))
    ((continuous_topologicalCovariantRangeAction F).comp
      (continuous_const.prodMk continuous_id))

theorem topologicalCovariantRangeCompHausContinuousTimeSlice_eq_iso_hom
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) :
    (fun y => topologicalCovariantRangeCompHausContinuousTimeSlice F t y) =
      ConcreteCategory.hom (topologicalCovariantRangeCompHausIso F t).hom := by
  funext y
  change topologicalCovariantRangeAction F (t, y) =
    (topologicalCovariantRangeCompHausIso F t).hom y
  change operatorObservationRangeCompHausCovariantFlowHom F.base t
      (topologicalCovariantOperatorAction_continuous F t) y =
    (operatorObservationRangeCovariantFlowCompHausIso F.base t
      (topologicalCovariantOperatorAction_continuous F t)
      (topologicalCovariantOperatorAction_continuous F (-t))).hom y
  exact (operatorObservationRangeCovariantFlowCompHausIso_hom_apply
    F.base t (topologicalCovariantOperatorAction_continuous F t)
      (topologicalCovariantOperatorAction_continuous F (-t)) y).symm

@[simp] theorem topologicalCovariantRangeCompHausContinuousTimeSlice_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (y : operatorObservationRangeCompHaus S) :
    topologicalCovariantRangeCompHausContinuousTimeSlice F t y =
      topologicalCovariantRangeAction F (t, y) :=
  rfl

noncomputable def topologicalCovariantRangeCompHausContinuousOrbit
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (y : operatorObservationRangeCompHaus S) :
    C(ℝ, operatorObservationRangeCompHaus S) :=
  ContinuousMap.mk
    (fun t => topologicalCovariantRangeAction F (t, y))
    ((continuous_topologicalCovariantRangeAction F).comp
      (continuous_id.prodMk continuous_const))

@[simp] theorem topologicalCovariantRangeCompHausContinuousOrbit_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (y : operatorObservationRangeCompHaus S) (t : ℝ) :
    topologicalCovariantRangeCompHausContinuousOrbit F y t =
      topologicalCovariantRangeAction F (t, y) :=
  rfl

theorem topologicalCovariantRangeCompHausContinuousOrbit_zero
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (y : operatorObservationRangeCompHaus S) :
    topologicalCovariantRangeCompHausContinuousOrbit F y 0 = y := by
  exact topologicalCovariantRangeAction_zero F y

theorem topologicalCovariantRangeCompHausContinuousOrbit_add
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (y : operatorObservationRangeCompHaus S) (s t : ℝ) :
    topologicalCovariantRangeCompHausContinuousOrbit F y (s + t) =
      topologicalCovariantRangeCompHausContinuousOrbit F
        (topologicalCovariantRangeCompHausContinuousTimeSlice F t y) s := by
  exact topologicalCovariantRangeAction_add F s t y

theorem topologicalCovariantRangeCompHausContinuousTimeSlice_zero
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    topologicalCovariantRangeCompHausContinuousTimeSlice F 0 =
      ContinuousMap.id _ := by
  ext y
  exact topologicalCovariantRangeAction_zero F y

theorem topologicalCovariantRangeCompHausContinuousTimeSlice_add
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (s t : ℝ) :
    topologicalCovariantRangeCompHausContinuousTimeSlice F (s + t) =
      (topologicalCovariantRangeCompHausContinuousTimeSlice F s).comp
        (topologicalCovariantRangeCompHausContinuousTimeSlice F t) := by
  ext y
  exact topologicalCovariantRangeAction_add F s t y

theorem topologicalCovariantRangeCompHausContinuousTimeSlice_neg_comp
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) :
    (topologicalCovariantRangeCompHausContinuousTimeSlice F (-t)).comp
        (topologicalCovariantRangeCompHausContinuousTimeSlice F t) =
      ContinuousMap.id _ := by
  ext y
  change topologicalCovariantRangeAction F
    (-t, topologicalCovariantRangeAction F (t, y)) = y
  rw [← topologicalCovariantRangeAction_add F (-t) t y]
  rw [neg_add_cancel]
  exact topologicalCovariantRangeAction_zero F y

theorem topologicalCovariantRangeCompHausContinuousTimeSlice_comp_neg
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) :
    (topologicalCovariantRangeCompHausContinuousTimeSlice F t).comp
        (topologicalCovariantRangeCompHausContinuousTimeSlice F (-t)) =
      ContinuousMap.id _ := by
  ext y
  change topologicalCovariantRangeAction F
    (t, topologicalCovariantRangeAction F (-t, y)) = y
  rw [← topologicalCovariantRangeAction_add F t (-t) y]
  rw [add_neg_cancel]
  exact topologicalCovariantRangeAction_zero F y

noncomputable def topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) :
    operatorObservationRangeCompHaus S ≃ₜ operatorObservationRangeCompHaus S :=
  { toFun := topologicalCovariantRangeCompHausContinuousTimeSlice F t
    invFun := topologicalCovariantRangeCompHausContinuousTimeSlice F (-t)
    left_inv := by
      intro y
      have h := congrArg
        (fun f => f y)
        (topologicalCovariantRangeCompHausContinuousTimeSlice_neg_comp F t)
      simpa using h
    right_inv := by
      intro y
      have h := congrArg
        (fun f => f y)
        (topologicalCovariantRangeCompHausContinuousTimeSlice_comp_neg F t)
      simpa using h
    continuous_toFun :=
      (topologicalCovariantRangeCompHausContinuousTimeSlice F t).continuous
    continuous_invFun :=
      (topologicalCovariantRangeCompHausContinuousTimeSlice F (-t)).continuous }

@[simp] theorem topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (y : operatorObservationRangeCompHaus S) :
    topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F t y =
      topologicalCovariantRangeAction F (t, y) :=
  rfl

theorem topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph_zero
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F 0 =
      Homeomorph.refl _ := by
  ext y
  exact topologicalCovariantRangeAction_zero F y

theorem topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph_add
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (s t : ℝ) :
    topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F (s + t) =
      (topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F t).trans
        (topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F s) := by
  ext y
  exact topologicalCovariantRangeAction_add F s t y

theorem topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph_neg
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) :
    topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F (-t) =
      (topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F t).symm := by
  ext y
  apply (topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F t).injective
  have h := congrArg
    (fun f => f y)
    (topologicalCovariantRangeCompHausContinuousTimeSlice_comp_neg F t)
  simpa [topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph] using h

@[simp] theorem topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph_neg_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (y : operatorObservationRangeCompHaus S) :
    topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F (-t) y =
      (topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F t).symm y := by
  rw [topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph_neg]

@[simp] theorem topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph_eq_compHausIso_hom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (y : operatorObservationRangeCompHaus S) :
    topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F t y =
      (topologicalCovariantRangeCompHausIso F t).hom y := by
  change topologicalCovariantRangeAction F (t, y) =
    (topologicalCovariantRangeCompHausIso F t).hom y
  change operatorObservationRangeCompHausCovariantFlowHom F.base t
      (topologicalCovariantOperatorAction_continuous F t) y =
    (operatorObservationRangeCovariantFlowCompHausIso F.base t
      (topologicalCovariantOperatorAction_continuous F t)
      (topologicalCovariantOperatorAction_continuous F (-t))).hom y
  exact (operatorObservationRangeCovariantFlowCompHausIso_hom_apply
    F.base t (topologicalCovariantOperatorAction_continuous F t)
      (topologicalCovariantOperatorAction_continuous F (-t)) y).symm

@[simp] theorem topologicalCovariantRangeCompHausContinuousOrbit_eq_homeomorph_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (y : operatorObservationRangeCompHaus S) (t : ℝ) :
    topologicalCovariantRangeCompHausContinuousOrbit F y t =
      topologicalCovariantRangeCompHausContinuousTimeSliceHomeomorph F t y :=
  rfl

noncomputable def topologicalCovariantRangeAddAction
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    AddAction ℝ (operatorObservationRangeCompHaus S) := by
  letI : VAdd ℝ (operatorObservationRangeCompHaus S) :=
    ⟨fun t y => topologicalCovariantRangeAction F (t, y)⟩
  letI : AddSemigroupAction ℝ (operatorObservationRangeCompHaus S) :=
    { add_vadd := by
        intro s t y
        exact topologicalCovariantRangeAction_add F s t y }
  exact
    { zero_vadd := by
        intro y
        exact topologicalCovariantRangeAction_zero F y }

@[simp] theorem topologicalCovariantRangeAddAction_vadd
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (y : operatorObservationRangeCompHaus S) :
    @VAdd.vadd ℝ (operatorObservationRangeCompHaus S)
        (topologicalCovariantRangeAddAction F).toAddSemigroupAction.toVAdd t y =
      topologicalCovariantRangeAction F (t, y) :=
  rfl

theorem topologicalCovariantRangeAddAction_continuous
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    letI : AddAction ℝ (operatorObservationRangeCompHaus S) :=
      topologicalCovariantRangeAddAction F
    Continuous (fun p : ℝ × operatorObservationRangeCompHaus S =>
      p.1 +ᵥ p.2) := by
  letI : AddAction ℝ (operatorObservationRangeCompHaus S) :=
    topologicalCovariantRangeAddAction F
  change Continuous (fun p : ℝ × operatorObservationRangeCompHaus S =>
    topologicalCovariantRangeAction F (p.1, p.2))
  exact continuous_topologicalCovariantRangeAction F

noncomputable def topologicalCovariantRangeContinuousVAdd
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    letI : AddAction ℝ (operatorObservationRangeCompHaus S) :=
      topologicalCovariantRangeAddAction F
    ContinuousVAdd ℝ (operatorObservationRangeCompHaus S) := by
  letI : AddAction ℝ (operatorObservationRangeCompHaus S) :=
    topologicalCovariantRangeAddAction F
  exact ⟨topologicalCovariantRangeAddAction_continuous F⟩

noncomputable def topologicalCovariantRangeContinuousConstVAdd
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    letI : AddAction ℝ (operatorObservationRangeCompHaus S) :=
      topologicalCovariantRangeAddAction F
    ContinuousConstVAdd ℝ (operatorObservationRangeCompHaus S) := by
  letI : AddAction ℝ (operatorObservationRangeCompHaus S) :=
    topologicalCovariantRangeAddAction F
  constructor
  intro t
  change Continuous (fun y : operatorObservationRangeCompHaus S =>
    topologicalCovariantRangeAction F (t, y))
  exact (topologicalCovariantRangeCompHausContinuousTimeSlice F t).continuous

theorem topologicalCovariantRangeCompHausContinuousAction_eq_vadd
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    letI : AddAction ℝ (operatorObservationRangeCompHaus S) :=
      topologicalCovariantRangeAddAction F
    topologicalCovariantRangeCompHausContinuousAction F =
      ContinuousMap.mk
        (fun p : ℝ × operatorObservationRangeCompHaus S => p.1 +ᵥ p.2)
        (topologicalCovariantRangeAddAction_continuous F) := by
  letI : AddAction ℝ (operatorObservationRangeCompHaus S) :=
    topologicalCovariantRangeAddAction F
  ext p
  rfl

@[simp] theorem topologicalCovariantRangeCompHausIso_hom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (t : ℝ)
    (y : operatorObservationRangeCompHaus S) :
    (topologicalCovariantRangeCompHausIso F t).hom y =
      operatorObservationRangeCompHausCovariantFlowHom F.base t
        (topologicalCovariantOperatorAction_continuous F t) y := by
  exact operatorObservationRangeCovariantFlowCompHausIso_hom_apply
    F.base t (topologicalCovariantOperatorAction_continuous F t)
      (topologicalCovariantOperatorAction_continuous F (-t)) y

theorem topologicalCovariantRangeCompHausIso_zero
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    (topologicalCovariantRangeCompHausIso F 0).hom =
      𝟙 (operatorObservationRangeCompHaus S) := by
  apply ConcreteCategory.hom_ext
  intro y
  apply Subtype.ext
  funext i
  change F.base.operatorAction 0 (y.1 i) = y.1 i
  exact F.base.operatorAction_zero _

theorem topologicalCovariantRangeCompHausIso_add
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (s t : ℝ) :
    (topologicalCovariantRangeCompHausIso F (s + t)).hom =
      (topologicalCovariantRangeCompHausIso F t).hom ≫
        (topologicalCovariantRangeCompHausIso F s).hom := by
  apply ConcreteCategory.hom_ext
  intro y
  apply Subtype.ext
  funext i
  change F.base.operatorAction (s + t) (y.1 i) =
    F.base.operatorAction s (F.base.operatorAction t (y.1 i))
  exact F.base.operatorAction_add s t _

theorem topologicalCovariantRangeCompHausIso_inv_eq_neg_hom
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) (t : ℝ) :
    (topologicalCovariantRangeCompHausIso F t).inv =
      (topologicalCovariantRangeCompHausIso F (-t)).hom := by
  apply ConcreteCategory.hom_ext
  intro y
  apply Subtype.ext
  funext i
  change F.base.operatorAction (-t) (y.1 i) =
    F.base.operatorAction (-t) (y.1 i)
  rfl

noncomputable def topologicalCovariantRangeCompHausTimeNatIso
    {S : NoncommutativeObservableSystem X A ι}
    (t : ℝ) :
    operatorObservationRangeCompHausFunctor (S := S) ≅
      operatorObservationRangeCompHausFunctor (S := S) :=
  NatIso.ofComponents
    (fun F => topologicalCovariantRangeCompHausIso F t)
    (by
      intro F G f
      apply ConcreteCategory.hom_ext
      intro y
      change (topologicalCovariantRangeCompHausIso G t).hom
            (operatorObservationRangeCompHausHomOfMorphism f y) =
          operatorObservationRangeCompHausHomOfMorphism f
            ((topologicalCovariantRangeCompHausIso F t).hom y)
      apply Subtype.ext
      funext i
      change G.base.operatorAction t (f.operatorMap (y.1 i)) =
        f.operatorMap (F.base.operatorAction t (y.1 i))
      exact (f.operatorAction_natural t (y.1 i)).symm)

theorem topologicalCovariantRangeCompHausTimeNatIso_zero
    {S : NoncommutativeObservableSystem X A ι} :
    topologicalCovariantRangeCompHausTimeNatIso (S := S) 0 =
      Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro y
  exact congrArg (fun h => h y)
    (topologicalCovariantRangeCompHausIso_zero F)

theorem topologicalCovariantRangeCompHausTimeNatIso_add
    {S : NoncommutativeObservableSystem X A ι} (s t : ℝ) :
    topologicalCovariantRangeCompHausTimeNatIso (S := S) (s + t) =
      (topologicalCovariantRangeCompHausTimeNatIso (S := S) t).trans
        (topologicalCovariantRangeCompHausTimeNatIso (S := S) s) := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro y
  exact congrArg (fun h => h y)
    (topologicalCovariantRangeCompHausIso_add F s t)

theorem topologicalCovariantRangeCompHausTimeNatIso_inv_eq_neg_hom
    {S : NoncommutativeObservableSystem X A ι} (t : ℝ) :
    (topologicalCovariantRangeCompHausTimeNatIso (S := S) t).inv =
      (topologicalCovariantRangeCompHausTimeNatIso (S := S) (-t)).hom := by
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro y
  exact congrArg (fun h => h y)
    (topologicalCovariantRangeCompHausIso_inv_eq_neg_hom F t)

theorem topologicalCovariantRangeCompHausTimeNatIso_eq_neg_symm
    {S : NoncommutativeObservableSystem X A ι} (t : ℝ) :
    topologicalCovariantRangeCompHausTimeNatIso (S := S) t =
      (topologicalCovariantRangeCompHausTimeNatIso (S := S) (-t)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro y
  change (topologicalCovariantRangeCompHausTimeNatIso (S := S) t).hom.app F y =
    (topologicalCovariantRangeCompHausTimeNatIso (S := S) (-t)).inv.app F y
  have h := congrArg (fun h => h.app F y)
    (topologicalCovariantRangeCompHausTimeNatIso_inv_eq_neg_hom (S := S) (-t))
  simpa only [neg_neg] using h.symm

theorem topologicalCovariantRangeAction_readout_covariant
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (x : X) :
    topologicalCovariantRangeAction F
        (t, ⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩) =
      ⟨S.operatorObservationMap (F.base.act t x),
        ⟨F.base.act t x, rfl⟩⟩ := by
  apply Subtype.ext
  funext i
  change F.base.operatorAction t ((S.operatorObservationMap x) i) =
    (S.operatorObservationMap (F.base.act t x)) i
  change F.base.operatorAction t ((S.observable i).eval x) =
    (S.observable i).eval (F.base.act t x)
  rw [F.base.observation_covariant]

theorem topologicalCovariantRangeCompHausIso_readout_covariant
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (x : X) :
    (topologicalCovariantRangeCompHausIso F t).hom
        ⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩ =
      ⟨S.operatorObservationMap (F.base.act t x),
        ⟨F.base.act t x, rfl⟩⟩ := by
  change topologicalCovariantRangeAction F
      (t, ⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩) =
    ⟨S.operatorObservationMap (F.base.act t x),
      ⟨F.base.act t x, rfl⟩⟩
  exact topologicalCovariantRangeAction_readout_covariant F t x

noncomputable def topologicalCovariantQuotientCompHausTimeNatIso
    {S : NoncommutativeObservableSystem X A ι}
    (t : ℝ) :
    operatorObservationQuotientCompHausFunctor (S := S) ≅
      operatorObservationQuotientCompHausFunctor (S := S) :=
  (operatorObservationQuotientRangeCompHausIso (S := S)).trans
    ((topologicalCovariantRangeCompHausTimeNatIso (S := S) t).trans
      (operatorObservationQuotientRangeCompHausIso (S := S)).symm)

@[simp] theorem topologicalCovariantQuotientCompHausTimeNatIso_hom_app
    {S : NoncommutativeObservableSystem X A ι}
    (t : ℝ) (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    (topologicalCovariantQuotientCompHausTimeNatIso (S := S) t).hom.app F =
      (operatorObservationQuotientRangeCompHausIso (S := S)).hom.app F ≫
        (topologicalCovariantRangeCompHausTimeNatIso (S := S) t).hom.app F ≫
        (operatorObservationQuotientRangeCompHausIso (S := S)).inv.app F := by
  rfl

@[simp] theorem topologicalCovariantQuotientCompHausTimeNatIso_inv_app
    {S : NoncommutativeObservableSystem X A ι}
    (t : ℝ) (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    (topologicalCovariantQuotientCompHausTimeNatIso (S := S) t).inv.app F =
      (operatorObservationQuotientRangeCompHausIso (S := S)).hom.app F ≫
        (topologicalCovariantRangeCompHausTimeNatIso (S := S) t).inv.app F ≫
        (operatorObservationQuotientRangeCompHausIso (S := S)).inv.app F := by
  rfl

theorem topologicalCovariantQuotientCompHausTimeNatIso_zero
    {S : NoncommutativeObservableSystem X A ι} :
    topologicalCovariantQuotientCompHausTimeNatIso (S := S) 0 =
      Iso.refl _ := by
  apply Iso.ext
  ext F
  simp [topologicalCovariantQuotientCompHausTimeNatIso,
    topologicalCovariantRangeCompHausTimeNatIso_zero, Category.assoc]

theorem topologicalCovariantQuotientCompHausTimeNatIso_add
    {S : NoncommutativeObservableSystem X A ι} (s t : ℝ) :
    topologicalCovariantQuotientCompHausTimeNatIso (S := S) (s + t) =
      (topologicalCovariantQuotientCompHausTimeNatIso (S := S) t).trans
        (topologicalCovariantQuotientCompHausTimeNatIso (S := S) s) := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro q
  simp [topologicalCovariantQuotientCompHausTimeNatIso,
    topologicalCovariantRangeCompHausTimeNatIso_add, Category.assoc]

theorem topologicalCovariantQuotientCompHausTimeNatIso_inv_eq_neg_hom
    {S : NoncommutativeObservableSystem X A ι} (t : ℝ) :
    (topologicalCovariantQuotientCompHausTimeNatIso (S := S) t).inv =
      (topologicalCovariantQuotientCompHausTimeNatIso (S := S) (-t)).hom := by
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro q
  simp [topologicalCovariantQuotientCompHausTimeNatIso,
    topologicalCovariantRangeCompHausTimeNatIso_inv_eq_neg_hom, Category.assoc]

noncomputable def topologicalCovariantQuotientCompHausContinuousAction
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S) :
    C(ℝ × operatorObservationQuotientCompHaus S,
      operatorObservationQuotientCompHaus S) := by
  let e := operatorObservationQuotientRangeHomeomorph S
  exact ContinuousMap.mk
    (fun p => e.symm (topologicalCovariantRangeAction F (p.1, e p.2)))
    (e.continuous_invFun.comp <|
      (continuous_topologicalCovariantRangeAction F).comp <|
        continuous_fst.prodMk (e.continuous_toFun.comp continuous_snd))

@[simp] theorem topologicalCovariantQuotientCompHausContinuousAction_apply
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (t : ℝ) (q : operatorObservationQuotientCompHaus S) :
    topologicalCovariantQuotientCompHausContinuousAction F (t, q) =
      (operatorObservationQuotientCompHausIso S).inv
        ((topologicalCovariantRangeCompHausIso F t).hom
          ((operatorObservationQuotientCompHausIso S).hom q)) := by
  rfl

theorem topologicalCovariantQuotientCompHausContinuousAction_zero
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (q : operatorObservationQuotientCompHaus S) :
    topologicalCovariantQuotientCompHausContinuousAction F (0, q) = q := by
  change (operatorObservationQuotientCompHausIso S).inv
      ((topologicalCovariantRangeCompHausIso F 0).hom
        ((operatorObservationQuotientCompHausIso S).hom q)) = q
  rw [topologicalCovariantRangeCompHausIso_zero]
  have hcancel :
      (operatorObservationQuotientCompHausIso S).inv
          ((operatorObservationQuotientCompHausIso S).hom q) = q := by
    simpa only [ConcreteCategory.comp_apply] using congrArg (fun h => h q)
      (operatorObservationQuotientCompHausIso S).hom_inv_id
  simpa using hcancel

theorem topologicalCovariantQuotientCompHausContinuousAction_add
    {S : NoncommutativeObservableSystem X A ι}
    (F : NoncommutativeObservableTopologicalCovariantFlow S)
    (s t : ℝ) (q : operatorObservationQuotientCompHaus S) :
    topologicalCovariantQuotientCompHausContinuousAction F (s + t, q) =
      topologicalCovariantQuotientCompHausContinuousAction F
        (s, topologicalCovariantQuotientCompHausContinuousAction F (t, q)) := by
  change (operatorObservationQuotientCompHausIso S).inv
      ((topologicalCovariantRangeCompHausIso F (s + t)).hom
        ((operatorObservationQuotientCompHausIso S).hom q)) =
    (operatorObservationQuotientCompHausIso S).inv
      ((topologicalCovariantRangeCompHausIso F s).hom
        ((operatorObservationQuotientCompHausIso S).hom
          ((operatorObservationQuotientCompHausIso S).inv
            ((topologicalCovariantRangeCompHausIso F t).hom
              ((operatorObservationQuotientCompHausIso S).hom q)))))
  rw [topologicalCovariantRangeCompHausIso_add]
  simp only [ConcreteCategory.comp_apply]
  have hcancel :
      (operatorObservationQuotientCompHausIso S).hom
          ((operatorObservationQuotientCompHausIso S).inv
            ((topologicalCovariantRangeCompHausIso F t).hom
              ((operatorObservationQuotientCompHausIso S).hom q))) =
        (topologicalCovariantRangeCompHausIso F t).hom
          ((operatorObservationQuotientCompHausIso S).hom q) := by
    simpa only [ConcreteCategory.comp_apply] using congrArg
      (fun h => h ((topologicalCovariantRangeCompHausIso F t).hom
        ((operatorObservationQuotientCompHausIso S).hom q)))
      (operatorObservationQuotientCompHausIso S).inv_hom_id
  rw [hcancel]

end InfoGeometry.Topology
