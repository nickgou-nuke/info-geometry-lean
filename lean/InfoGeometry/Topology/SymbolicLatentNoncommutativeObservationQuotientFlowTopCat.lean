import Mathlib
import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationTopCat

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u} [TopologicalSpace X] [NormedRing A] [Fintype ι]

/-!
# Quotient flow of operator-valued symbolic-latent observations

This owner extends the native operator-valued observation quotient with a
flow that preserves the complete observation profile in `A`.  The quotient
descent is therefore a quotient of a potentially noncommutative observation
profile.  The quotient carrier itself is only a topological quotient; no
algebra or involution is inferred on it.
-/

structure NoncommutativeObservableFlow
    (S : NoncommutativeObservableSystem X A ι) where
  act : ℝ → X → X
  act_zero : ∀ x, act 0 x = x
  act_add : ∀ s t x, act (s + t) x = act s (act t x)
  continuous_act : Continuous (fun p : ℝ × X => act p.1 p.2)
  preserves_observation : ∀ t x,
    S.operatorObservationMap (act t x) = S.operatorObservationMap x

theorem operatorCommutatorProfile_flow_invariant
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ) (x : X) :
    operatorCommutatorProfile S (Φ.act t x) =
      operatorCommutatorProfile S x := by
  have hobs := Φ.preserves_observation t x
  funext i j
  change operatorCommutator
      ((S.observable i).eval (Φ.act t x))
      ((S.observable j).eval (Φ.act t x)) =
    operatorCommutator ((S.observable i).eval x) ((S.observable j).eval x)
  have hi := congrFun hobs i
  have hj := congrFun hobs j
  change (S.observable i).eval (Φ.act t x) =
    (S.observable i).eval x at hi
  change (S.observable j).eval (Φ.act t x) =
    (S.observable j).eval x at hj
  rw [hi, hj]

theorem operatorCommutingLocus_flow_iff
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ) (x : X) :
    Φ.act t x ∈ operatorCommutingLocus S ↔
      x ∈ operatorCommutingLocus S := by
  change operatorCommutatorProfile S (Φ.act t x) = 0 ↔
    operatorCommutatorProfile S x = 0
  rw [operatorCommutatorProfile_flow_invariant Φ t x]

theorem observationFunctional_flow_invariant
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    {B : Type*} (F : (ι → A) → B) (t : ℝ) (x : X) :
    F (S.operatorObservationMap (Φ.act t x)) =
      F (S.operatorObservationMap x) := by
  rw [Φ.preserves_observation t x]

def descendedOperatorObservationFlow
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ) :
    OperatorObservationalQuotient S → OperatorObservationalQuotient S :=
  Quotient.lift
    (fun x => operatorObservationQuotientMap S (Φ.act t x))
    (by
      intro x y hxy
      apply Quotient.sound
      change S.operatorObservationMap (Φ.act t x) =
        S.operatorObservationMap (Φ.act t y)
      rw [Φ.preserves_observation t x, Φ.preserves_observation t y, hxy])

theorem descendedOperatorObservationFlow_mk
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ) (x : X) :
    descendedOperatorObservationFlow Φ t
        (operatorObservationQuotientMap S x) =
      operatorObservationQuotientMap S (Φ.act t x) := rfl

@[simp] theorem descendedOperatorObservationFlow_apply_eq
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ)
    (q : OperatorObservationalQuotient S) :
    descendedOperatorObservationFlow Φ t q = q := by
  refine Quotient.inductionOn q ?_
  intro x
  change descendedOperatorObservationFlow Φ t
      (operatorObservationQuotientMap S x) =
    operatorObservationQuotientMap S x
  rw [descendedOperatorObservationFlow_mk]
  apply Quotient.sound
  change S.operatorObservationMap (Φ.act t x) =
    S.operatorObservationMap x
  exact Φ.preserves_observation t x

@[simp] theorem descendedOperatorObservationFlow_eq_id
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ) :
    descendedOperatorObservationFlow Φ t = id := by
  funext q
  exact descendedOperatorObservationFlow_apply_eq Φ t q

theorem continuous_descendedOperatorObservationFlow
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S) (t : ℝ) :
    Continuous (descendedOperatorObservationFlow Φ t) := by
  apply Continuous.quotient_lift
  · exact (continuous_operatorObservationQuotientMap S).comp
      (Φ.continuous_act.comp (continuous_const.prodMk continuous_id))

theorem descendedOperatorObservationFlow_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (q : OperatorObservationalQuotient S) :
    descendedOperatorObservationFlow Φ 0 q = q := by
  refine Quotient.inductionOn q ?_
  intro x
  change descendedOperatorObservationFlow Φ 0
      (operatorObservationQuotientMap S x) =
    operatorObservationQuotientMap S x
  calc
    descendedOperatorObservationFlow Φ 0 (operatorObservationQuotientMap S x) =
        operatorObservationQuotientMap S (Φ.act 0 x) :=
      descendedOperatorObservationFlow_mk Φ 0 x
    _ = operatorObservationQuotientMap S x := by rw [Φ.act_zero]

theorem descendedOperatorObservationFlow_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (s t : ℝ) (q : OperatorObservationalQuotient S) :
    descendedOperatorObservationFlow Φ (s + t) q =
      descendedOperatorObservationFlow Φ s
        (descendedOperatorObservationFlow Φ t q) := by
  refine Quotient.inductionOn q ?_
  intro x
  change descendedOperatorObservationFlow Φ (s + t)
      (operatorObservationQuotientMap S x) =
    descendedOperatorObservationFlow Φ s
      (descendedOperatorObservationFlow Φ t
        (operatorObservationQuotientMap S x))
  calc
    descendedOperatorObservationFlow Φ (s + t)
        (operatorObservationQuotientMap S x) =
        operatorObservationQuotientMap S (Φ.act (s + t) x) :=
      descendedOperatorObservationFlow_mk Φ (s + t) x
    _ = operatorObservationQuotientMap S (Φ.act s (Φ.act t x)) := by
      rw [Φ.act_add]
    _ = descendedOperatorObservationFlow Φ s
        (descendedOperatorObservationFlow Φ t
          (operatorObservationQuotientMap S x)) := by
      rw [descendedOperatorObservationFlow_mk, descendedOperatorObservationFlow_mk]

def descendedOperatorObservationFlowTopCatHom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    TopCat.of (OperatorObservationalQuotient S) ⟶
      TopCat.of (OperatorObservationalQuotient S) :=
    TopCat.ofHom
    { toFun := descendedOperatorObservationFlow Φ t
      continuous_toFun := by
        exact h_cont.comp (continuous_const.prodMk continuous_id) }

@[simp] theorem descendedOperatorObservationFlowTopCatHom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (t : ℝ) (q : OperatorObservationalQuotient S) :
    descendedOperatorObservationFlowTopCatHom Φ h_cont t q =
      descendedOperatorObservationFlow Φ t q := rfl

theorem descendedOperatorObservationFlowTopCatHom_zero
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2)) :
    descendedOperatorObservationFlowTopCatHom Φ h_cont 0 =
      𝟙 (TopCat.of (OperatorObservationalQuotient S)) := by
  ext q
  exact descendedOperatorObservationFlow_zero Φ q

theorem descendedOperatorObservationFlowTopCatHom_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (s t : ℝ) :
    descendedOperatorObservationFlowTopCatHom Φ h_cont (s + t) =
      descendedOperatorObservationFlowTopCatHom Φ h_cont s ≫
        descendedOperatorObservationFlowTopCatHom Φ h_cont t := by
  ext q
  dsimp [descendedOperatorObservationFlowTopCatHom]
  change descendedOperatorObservationFlow Φ (s + t) q =
    descendedOperatorObservationFlow Φ t
      (descendedOperatorObservationFlow Φ s q)
  rw [add_comm s t]
  exact descendedOperatorObservationFlow_add Φ t s q

theorem descendedOperatorObservationFlowTopCatHom_add_canonical
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (s t : ℝ) :
    descendedOperatorObservationFlowTopCatHom Φ h_cont (s + t) =
      descendedOperatorObservationFlowTopCatHom Φ h_cont t ≫
        descendedOperatorObservationFlowTopCatHom Φ h_cont s := by
  ext q
  dsimp [descendedOperatorObservationFlowTopCatHom]
  exact descendedOperatorObservationFlow_add Φ s t q

/-! A time slice on the operator-valued quotient is a homeomorphism.

The inverse is the negative-time slice.  This is a topological consequence
of the already-proved group laws and joint continuity property; it does not
collapse the operator-valued quotient to a scalar observable. -/
def descendedOperatorObservationFlowHomeomorph
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    OperatorObservationalQuotient S ≃ₜ OperatorObservationalQuotient S where
  toFun := descendedOperatorObservationFlow Φ t
  invFun := descendedOperatorObservationFlow Φ (-t)
  left_inv := by
    intro q
    calc
      descendedOperatorObservationFlow Φ (-t)
          (descendedOperatorObservationFlow Φ t q) =
          descendedOperatorObservationFlow Φ (-t + t) q := by
            exact (descendedOperatorObservationFlow_add Φ (-t) t q).symm
      _ = q := by
        rw [neg_add_cancel]
        exact descendedOperatorObservationFlow_zero Φ q
  right_inv := by
    intro q
    calc
      descendedOperatorObservationFlow Φ t
          (descendedOperatorObservationFlow Φ (-t) q) =
          descendedOperatorObservationFlow Φ (t + -t) q := by
            exact (descendedOperatorObservationFlow_add Φ t (-t) q).symm
      _ = q := by
        rw [add_neg_cancel]
        exact descendedOperatorObservationFlow_zero Φ q
  continuous_toFun := h_cont.comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := h_cont.comp
    (continuous_const.prodMk continuous_id)

@[simp] theorem descendedOperatorObservationFlowHomeomorph_eq_refl
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    descendedOperatorObservationFlowHomeomorph Φ h_cont t =
      Homeomorph.refl (OperatorObservationalQuotient S) := by
  ext q
  exact descendedOperatorObservationFlow_apply_eq Φ t q

@[simp] theorem descendedOperatorObservationFlowHomeomorph_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (t : ℝ) (q : OperatorObservationalQuotient S) :
    descendedOperatorObservationFlowHomeomorph Φ h_cont t q =
      descendedOperatorObservationFlow Φ t q :=
  rfl

theorem descendedOperatorObservationFlowHomeomorph_add
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (s t : ℝ) (q : OperatorObservationalQuotient S) :
    descendedOperatorObservationFlowHomeomorph Φ h_cont (s + t) q =
      descendedOperatorObservationFlowHomeomorph Φ h_cont s
        (descendedOperatorObservationFlowHomeomorph Φ h_cont t q) := by
  simpa only [descendedOperatorObservationFlowHomeomorph_apply] using
    descendedOperatorObservationFlow_add Φ s t q

theorem descendedOperatorObservationFlowHomeomorph_commutes_with_projection
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (t : ℝ) (x : X) :
    descendedOperatorObservationFlowHomeomorph Φ h_cont t
        (operatorObservationQuotientMap S x) =
      operatorObservationQuotientMap S (Φ.act t x) :=
  descendedOperatorObservationFlow_mk Φ t x

theorem descendedOperatorObservationFlow_commutes_with_projection
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableFlow S)
    (h_cont : Continuous (fun p : ℝ × OperatorObservationalQuotient S =>
      descendedOperatorObservationFlow Φ p.1 p.2))
    (t : ℝ) (x : X) :
    descendedOperatorObservationFlowTopCatHom Φ h_cont t
        (operatorObservationQuotientMap S x) =
      operatorObservationQuotientMap S (Φ.act t x) :=
  descendedOperatorObservationFlow_mk Φ t x

end InfoGeometry.Topology
