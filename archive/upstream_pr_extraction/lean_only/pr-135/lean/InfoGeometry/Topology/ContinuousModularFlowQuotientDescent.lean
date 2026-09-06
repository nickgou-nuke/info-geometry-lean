import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn

namespace InfoGeometry.Topology.ContinuousQuotientDescent

/-!
# Continuous descent of a discrete modular flow

This file separates the set-theoretic representative choice from the
topological statement.  The quotient map is the only descent property;
continuity is obtained from its universal property.
-/

structure ContinuousFlow (X : Type*) [TopologicalSpace X] where
  flow : ℤ → X → X
  zero_law : ∀ x, flow 0 x = x
  add_law : ∀ s t x, flow (s + t) x = flow s (flow t x)
  continuous : ∀ t, Continuous (flow t)

structure QuotientData
    (X Q : Type*) [TopologicalSpace X] [TopologicalSpace Q]
    (action : ContinuousFlow X) where
  proj : X → Q
  isQuotient : Topology.IsQuotientMap proj
  invariant : ∀ t x y, proj x = proj y →
    proj (action.flow t x) = proj (action.flow t y)

noncomputable def descended
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (t : ℤ) (y : Q) : Q :=
  q.proj (action.flow t (Classical.choose (q.isQuotient.surjective y)))

theorem descended_commutes
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (t : ℤ) (x : X) :
    descended q t (q.proj x) = q.proj (action.flow t x) := by
  unfold descended
  have hx :
      q.proj x =
        q.proj (Classical.choose (q.isQuotient.surjective (q.proj x))) := by
    symm
    exact Classical.choose_spec (q.isQuotient.surjective (q.proj x))
  exact (q.invariant t x _ hx).symm

theorem descended_unique
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (t : ℤ) (f : Q → Q)
    (hf : ∀ x, f (q.proj x) = q.proj (action.flow t x)) :
    f = descended q t := by
  funext y
  obtain ⟨x, rfl⟩ := q.isQuotient.surjective y
  rw [hf, descended_commutes]

theorem continuous_descended
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (t : ℤ) :
    Continuous (descended q t) := by
  apply q.isQuotient.continuous_iff.mpr
  have hcomm : descended q t ∘ q.proj = q.proj ∘ action.flow t := by
    funext x
    exact descended_commutes q t x
  rw [hcomm]
  exact q.isQuotient.continuous.comp (action.continuous t)

theorem continuous_descended_joint
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) :
    Continuous (fun p : ℤ × Q => descended q p.1 p.2) := by
  rw [continuous_prod_of_discrete_left]
  intro t
  simpa using continuous_descended q t

theorem descended_zero
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (y : Q) :
    descended q 0 y = y := by
  obtain ⟨x, rfl⟩ := q.isQuotient.surjective y
  rw [descended_commutes, action.zero_law]

theorem descended_add
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (s t : ℤ) (y : Q) :
    descended q (s + t) y = descended q s (descended q t y) := by
  obtain ⟨x, rfl⟩ := q.isQuotient.surjective y
  rw [descended_commutes, action.add_law, descended_commutes,
    descended_commutes]

noncomputable def descended_homeomorph
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {action : ContinuousFlow X}
    (q : QuotientData X Q action) (t : ℤ) : Q ≃ₜ Q :=
  { toFun := descended q t
    invFun := descended q (-t)
    left_inv := by
      intro y
      rw [← descended_add q (-t) t y]
      simpa [add_comm] using descended_zero q y
    right_inv := by
      intro y
      rw [← descended_add q t (-t) y]
      simpa using descended_zero q y
    continuous_toFun := continuous_descended q t
    continuous_invFun := continuous_descended q (-t) }

end InfoGeometry.Topology.ContinuousQuotientDescent
