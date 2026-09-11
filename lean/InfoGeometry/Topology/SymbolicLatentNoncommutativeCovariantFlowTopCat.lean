import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationQuotientFlowTopCat

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u} [TopologicalSpace X] [NormedRing A]
  [StarRing A] [Algebra ℂ A] [Fintype ι]

/-!
# Covariant noncommutative symbolic-latent flows

The profile-preserving owner collapses its observational quotient flow to the
identity.  This owner records the nontrivial alternative: observations may be
transported by a `StarAlgEquiv` of the target algebra.  The quotient carrier
is still only a topological quotient; the algebraic operations remain in the
observation target.
-/

structure NoncommutativeObservableCovariantFlow
    (S : NoncommutativeObservableSystem X A ι) where
  act : ℝ → X → X
  act_zero : ∀ x, act 0 x = x
  act_add : ∀ s t x, act (s + t) x = act s (act t x)
  continuous_act : Continuous (fun p : ℝ × X => act p.1 p.2)
  operatorAction : ℝ → A ≃⋆ₐ[ℂ] A
  operatorAction_zero : ∀ a, operatorAction 0 a = a
  operatorAction_add : ∀ s t a,
    operatorAction (s + t) a =
      operatorAction s (operatorAction t a)
  observation_covariant : ∀ t x i,
    (S.observable i).eval (act t x) =
      operatorAction t ((S.observable i).eval x)

theorem operatorCommutatorProfile_covariant
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (t : ℝ) (x : X) :
    operatorCommutatorProfile S (Φ.act t x) =
      fun i j => Φ.operatorAction t
        (operatorCommutator ((S.observable i).eval x)
          ((S.observable j).eval x)) := by
  funext i j
  change operatorCommutator
      ((S.observable i).eval (Φ.act t x))
      ((S.observable j).eval (Φ.act t x)) = _
  rw [Φ.observation_covariant t x i,
    Φ.observation_covariant t x j]
  simp [operatorCommutator]

theorem operatorCommutingLocus_covariant_iff
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (t : ℝ) (x : X) :
    Φ.act t x ∈ operatorCommutingLocus S ↔
      x ∈ operatorCommutingLocus S := by
  change operatorCommutatorProfile S (Φ.act t x) = 0 ↔
    operatorCommutatorProfile S x = 0
  rw [operatorCommutatorProfile_covariant Φ t x]
  constructor
  · intro h
    have h' := congrArg (fun f : ι → ι → A =>
      fun i j => (Φ.operatorAction t).symm (f i j)) h
    funext i j
    have hij := congrFun (congrFun h' i) j
    simpa using hij
  · intro h
    funext i j
    have hij := congrFun (congrFun h i) j
    change Φ.operatorAction t
        (operatorCommutator ((S.observable i).eval x)
          ((S.observable j).eval x)) = 0
    simpa using congrArg (Φ.operatorAction t) hij

def descendedCovariantOperatorObservationFlow
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    OperatorObservationalQuotient S → OperatorObservationalQuotient S :=
  Quotient.lift
    (fun x => operatorObservationQuotientMap S (Φ.act t x))
    (by
      intro x y hxy
      apply Quotient.sound
      change S.operatorObservationMap x =
        S.operatorObservationMap y at hxy
      change S.operatorObservationMap (Φ.act t x) =
        S.operatorObservationMap (Φ.act t y)
      funext i
      change (S.observable i).eval (Φ.act t x) =
        (S.observable i).eval (Φ.act t y)
      rw [Φ.observation_covariant t x i,
        Φ.observation_covariant t y i]
      have hi := congrFun hxy i
      change (S.observable i).eval x =
        (S.observable i).eval y at hi
      rw [hi])

@[simp] theorem descendedCovariantOperatorObservationFlow_mk
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) (x : X) :
    descendedCovariantOperatorObservationFlow Φ t
        (operatorObservationQuotientMap S x) =
      operatorObservationQuotientMap S (Φ.act t x) :=
  rfl

theorem operatorObservationQuotientReadout_covariant
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (t : ℝ) (q : OperatorObservationalQuotient S) :
    operatorObservationQuotientReadout S
        (descendedCovariantOperatorObservationFlow Φ t q) =
      fun i => Φ.operatorAction t
        (operatorObservationQuotientReadout S q i) := by
  refine Quotient.inductionOn q ?_
  intro x
  change S.operatorObservationMap (Φ.act t x) = _
  funext i
  change (S.observable i).eval (Φ.act t x) = _
  rw [Φ.observation_covariant t x i]
  rfl

theorem operatorCommutatorProfileQuotientReadout_covariant
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (t : ℝ) (q : OperatorObservationalQuotient S) :
    operatorCommutatorProfileQuotientReadout S
        (descendedCovariantOperatorObservationFlow Φ t q) =
      fun i j => Φ.operatorAction t
        (operatorCommutatorProfileQuotientReadout S q i j) := by
  refine Quotient.inductionOn q ?_
  intro x
  change operatorCommutatorProfile S (Φ.act t x) = _
  exact operatorCommutatorProfile_covariant Φ t x

theorem descendedCovariantOperatorObservationFlow_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (q : OperatorObservationalQuotient S) :
    descendedCovariantOperatorObservationFlow Φ 0 q = q := by
  refine Quotient.inductionOn q ?_
  intro x
  change descendedCovariantOperatorObservationFlow Φ 0
      (operatorObservationQuotientMap S x) =
    operatorObservationQuotientMap S x
  rw [descendedCovariantOperatorObservationFlow_mk, Φ.act_zero]

theorem descendedCovariantOperatorObservationFlow_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (s t : ℝ) (q : OperatorObservationalQuotient S) :
    descendedCovariantOperatorObservationFlow Φ (s + t) q =
      descendedCovariantOperatorObservationFlow Φ s
        (descendedCovariantOperatorObservationFlow Φ t q) := by
  refine Quotient.inductionOn q ?_
  intro x
  calc
    descendedCovariantOperatorObservationFlow Φ (s + t)
        (operatorObservationQuotientMap S x) =
        operatorObservationQuotientMap S (Φ.act (s + t) x) :=
      descendedCovariantOperatorObservationFlow_mk Φ (s + t) x
    _ = operatorObservationQuotientMap S (Φ.act s (Φ.act t x)) := by
      rw [Φ.act_add]
    _ = descendedCovariantOperatorObservationFlow Φ s
        (descendedCovariantOperatorObservationFlow Φ t
          (operatorObservationQuotientMap S x)) := by
      rw [descendedCovariantOperatorObservationFlow_mk,
        descendedCovariantOperatorObservationFlow_mk]

theorem continuous_descendedCovariantOperatorObservationFlow
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    Continuous (descendedCovariantOperatorObservationFlow Φ t) := by
  apply Continuous.quotient_lift
  exact (continuous_operatorObservationQuotientMap S).comp
    (Φ.continuous_act.comp (continuous_const.prodMk continuous_id))

def descendedCovariantOperatorObservationFlowHomeomorph
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedCovariantOperatorObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    OperatorObservationalQuotient S ≃ₜ OperatorObservationalQuotient S where
  toFun := descendedCovariantOperatorObservationFlow Φ t
  invFun := descendedCovariantOperatorObservationFlow Φ (-t)
  left_inv := by
    intro q
    calc
      descendedCovariantOperatorObservationFlow Φ (-t)
          (descendedCovariantOperatorObservationFlow Φ t q) =
          descendedCovariantOperatorObservationFlow Φ (-t + t) q := by
            exact (descendedCovariantOperatorObservationFlow_add Φ (-t) t q).symm
      _ = q := by
        rw [neg_add_cancel]
        exact descendedCovariantOperatorObservationFlow_zero Φ q
  right_inv := by
    intro q
    calc
      descendedCovariantOperatorObservationFlow Φ t
          (descendedCovariantOperatorObservationFlow Φ (-t) q) =
          descendedCovariantOperatorObservationFlow Φ (t + -t) q := by
            exact (descendedCovariantOperatorObservationFlow_add Φ t (-t) q).symm
      _ = q := by
        rw [add_neg_cancel]
        exact descendedCovariantOperatorObservationFlow_zero Φ q
  continuous_toFun := h_cont.comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := h_cont.comp
    (continuous_const.prodMk continuous_id)

@[simp] theorem descendedCovariantOperatorObservationFlowHomeomorph_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedCovariantOperatorObservationFlow Φ p.1 p.2))
    (t : ℝ) (q : OperatorObservationalQuotient S) :
    descendedCovariantOperatorObservationFlowHomeomorph Φ h_cont t q =
      descendedCovariantOperatorObservationFlow Φ t q :=
  rfl

theorem descendedCovariantOperatorObservationFlowHomeomorph_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedCovariantOperatorObservationFlow Φ p.1 p.2))
    (s t : ℝ) (q : OperatorObservationalQuotient S) :
    descendedCovariantOperatorObservationFlowHomeomorph Φ h_cont (s + t) q =
      descendedCovariantOperatorObservationFlowHomeomorph Φ h_cont s
        (descendedCovariantOperatorObservationFlowHomeomorph Φ h_cont t q) := by
  simpa only [descendedCovariantOperatorObservationFlowHomeomorph_apply] using
    descendedCovariantOperatorObservationFlow_add Φ s t q

def descendedCovariantOperatorObservationFlowTopCatHom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    TopCat.of (OperatorObservationalQuotient S) ⟶
      TopCat.of (OperatorObservationalQuotient S) :=
  TopCat.ofHom
    { toFun := descendedCovariantOperatorObservationFlow Φ t
      continuous_toFun := continuous_descendedCovariantOperatorObservationFlow Φ t }

@[simp] theorem descendedCovariantOperatorObservationFlowTopCatHom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (q : OperatorObservationalQuotient S) :
    descendedCovariantOperatorObservationFlowTopCatHom Φ t q =
      descendedCovariantOperatorObservationFlow Φ t q :=
  rfl

theorem descendedCovariantOperatorObservationFlowTopCatHom_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) :
    descendedCovariantOperatorObservationFlowTopCatHom Φ 0 =
      𝟙 (TopCat.of (OperatorObservationalQuotient S)) := by
  ext q
  exact descendedCovariantOperatorObservationFlow_zero Φ q

theorem descendedCovariantOperatorObservationFlowTopCatHom_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (s t : ℝ) :
    descendedCovariantOperatorObservationFlowTopCatHom Φ (s + t) =
      descendedCovariantOperatorObservationFlowTopCatHom Φ t ≫
        descendedCovariantOperatorObservationFlowTopCatHom Φ s := by
  ext q
  change descendedCovariantOperatorObservationFlow Φ (s + t) q =
    descendedCovariantOperatorObservationFlow Φ s
      (descendedCovariantOperatorObservationFlow Φ t q)
  exact descendedCovariantOperatorObservationFlow_add Φ s t q

theorem descendedCovariantOperatorObservationFlowTopCatHom_isIso
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    CategoryTheory.IsIso (descendedCovariantOperatorObservationFlowTopCatHom Φ t) := by
  refine CategoryTheory.IsIso.mk
    ⟨descendedCovariantOperatorObservationFlowTopCatHom Φ (-t), ?_, ?_⟩
  · apply TopCat.hom_ext
    ext q
    change descendedCovariantOperatorObservationFlow Φ (-t)
        (descendedCovariantOperatorObservationFlow Φ t q) = q
    calc
      descendedCovariantOperatorObservationFlow Φ (-t)
          (descendedCovariantOperatorObservationFlow Φ t q) =
          descendedCovariantOperatorObservationFlow Φ (-t + t) q :=
        (descendedCovariantOperatorObservationFlow_add Φ (-t) t q).symm
      _ = q := by
        rw [neg_add_cancel]
        exact descendedCovariantOperatorObservationFlow_zero Φ q
  · apply TopCat.hom_ext
    ext q
    change descendedCovariantOperatorObservationFlow Φ t
        (descendedCovariantOperatorObservationFlow Φ (-t) q) = q
    calc
      descendedCovariantOperatorObservationFlow Φ t
          (descendedCovariantOperatorObservationFlow Φ (-t) q) =
          descendedCovariantOperatorObservationFlow Φ (t + -t) q :=
        (descendedCovariantOperatorObservationFlow_add Φ t (-t) q).symm
      _ = q := by
        rw [add_neg_cancel]
        exact descendedCovariantOperatorObservationFlow_zero Φ q

end InfoGeometry.Topology
