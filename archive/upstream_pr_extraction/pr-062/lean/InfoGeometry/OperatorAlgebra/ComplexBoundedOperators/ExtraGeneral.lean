import Mathlib.Tactic

/-!
# AFP CBO `Extra_General` adapters

This file ports the reusable, Lean-native parts of AFP's `Extra_General`
support theory.  Isabelle-specific infrastructure is intentionally not copied;
the declarations below are small wrappers around Mathlib's choice, finite-sum,
closure, and complex-number APIs.
-/

noncomputable section

open scoped BigOperators
open Set

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace ExtraGeneral

theorem uniqueChoice {α β : Type*} {Q : α → β → Prop}
    (hQ : ∀ x, ∃! y, Q x y) :
    ∃! f : α → β, ∀ x, Q x (f x) := by
  classical
  refine ⟨fun x => Classical.choose (ExistsUnique.exists (hQ x)), ?_, ?_⟩
  · intro x
    exact Classical.choose_spec (ExistsUnique.exists (hQ x))
  · intro g hg
    funext x
    exact ExistsUnique.unique (hQ x)
      (hg x)
      (Classical.choose_spec (ExistsUnique.exists (hQ x)))

theorem finset_sum_single {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (s : Finset α) (f : α → β) (i : α)
    (hzero : ∀ j ∈ s, j ≠ i → f j = 0) :
    Finset.sum s f = if i ∈ s then f i else 0 := by
  classical
  by_cases hi : i ∈ s
  · simp [hi, Finset.sum_eq_single i (by
      intro j hj hji
      exact hzero j hj hji)]
  · have hzero' : ∀ j ∈ s, f j = 0 := by
      intro j hj
      exact hzero j hj (by
        intro hji
        exact hi (hji ▸ hj))
    simp [hi, Finset.sum_eq_zero hzero']

theorem eqOn_closure_of_continuous {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
    {s : Set α} {f g : α → β}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : EqOn f g s) :
    EqOn f g (closure s) := by
  intro x hx
  let Z : Set α := {x | f x = g x}
  have hclosed : IsClosed Z := isClosed_eq hf hg
  have hsZ : s ⊆ Z := by
    intro y hy
    exact hfg hy
  exact closure_minimal hsZ hclosed hx

theorem leOn_closure_of_continuous {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [LinearOrder β] [ClosedIciTopology β]
    [ClosedIicTopology β] [OrderClosedTopology β]
    {s : Set α} {f g : α → β}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    ∀ x ∈ closure s, f x ≤ g x := by
  intro x hx
  let Z : Set α := {x | f x ≤ g x}
  have hclosed : IsClosed Z := isClosed_le hf hg
  have hsZ : s ⊆ Z := by
    intro y hy
    exact hfg y hy
  exact closure_minimal hsZ hclosed hx

theorem complex_star_mul_self_eq_normSq (z : ℂ) :
    star z * z = (Complex.normSq z : ℂ) := by
  simp [Complex.normSq, Complex.ext_iff, pow_two, mul_comm, mul_left_comm, mul_assoc]

theorem complex_mul_star_self_eq_normSq (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  rw [mul_comm]
  exact complex_star_mul_self_eq_normSq z

theorem complex_star_mul_self_re_nonneg (z : ℂ) :
    0 ≤ (star z * z).re := by
  rw [complex_star_mul_self_eq_normSq]
  exact Complex.normSq_nonneg z

end ExtraGeneral
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
