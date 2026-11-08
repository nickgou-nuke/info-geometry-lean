import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

/-!
Generic quotient descent for an additive modular flow.  The action is the
native Mathlib `AddAction`; no representative is chosen and no continuity is
claimed without the corresponding quotient-topology property.
-/

def descendedModularFlow
    {X : Type*} (r : Setoid X) [AddAction ℤ X]
    (h_invariant : ∀ (t : ℤ) (x y : X), r.r x y →
      r.r (t +ᵥ x) (t +ᵥ y))
    (t : ℤ) : Quotient r → Quotient r :=
  Quotient.lift
    (fun x => Quotient.mk r (t +ᵥ x))
    (by
      intro x y hxy
      exact Quotient.sound (h_invariant t x y hxy))

@[simp] theorem descendedModularFlow_mk
    {X : Type*} (r : Setoid X) [AddAction ℤ X]
    (h_invariant : ∀ (t : ℤ) (x y : X), r.r x y →
      r.r (t +ᵥ x) (t +ᵥ y))
    (t : ℤ) (x : X) :
    descendedModularFlow r h_invariant t (Quotient.mk r x) =
      Quotient.mk r (t +ᵥ x) :=
  rfl

theorem descendedModularFlow_zero
    {X : Type*} (r : Setoid X) [AddAction ℤ X]
    (h_invariant : ∀ (t : ℤ) (x y : X), r.r x y →
      r.r (t +ᵥ x) (t +ᵥ y))
    (q : Quotient r) :
    descendedModularFlow r h_invariant 0 q = q := by
  induction q using Quotient.inductionOn with
  | h x =>
      rw [descendedModularFlow_mk, zero_vadd]

theorem descendedModularFlow_add
    {X : Type*} (r : Setoid X) [AddAction ℤ X]
    (h_invariant : ∀ (t : ℤ) (x y : X), r.r x y →
      r.r (t +ᵥ x) (t +ᵥ y))
    (s t : ℤ) (q : Quotient r) :
    descendedModularFlow r h_invariant (s + t) q =
      descendedModularFlow r h_invariant s
        (descendedModularFlow r h_invariant t q) := by
  induction q using Quotient.inductionOn with
  | h x =>
      rw [descendedModularFlow_mk, descendedModularFlow_mk,
        descendedModularFlow_mk, add_vadd]

theorem descendedModularFlow_commutes_with_quotient_mk
    {X : Type*} (r : Setoid X) [AddAction ℤ X]
    (h_invariant : ∀ (t : ℤ) (x y : X), r.r x y →
      r.r (t +ᵥ x) (t +ᵥ y))
    (t : ℤ) (x : X) :
    descendedModularFlow r h_invariant t (Quotient.mk r x) =
      Quotient.mk r (t +ᵥ x) :=
  descendedModularFlow_mk r h_invariant t x

theorem continuous_descendedModularFlow_fixed
    {X : Type*} [TopologicalSpace X]
    (r : Setoid X) [AddAction ℤ X]
    (h_invariant : ∀ (t : ℤ) (x y : X), r.r x y →
      r.r (t +ᵥ x) (t +ᵥ y))
    (t : ℤ) (h_cont : Continuous (fun x : X => t +ᵥ x)) :
    Continuous (descendedModularFlow r h_invariant t) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp h_cont

end InfoGeometry.Topology
