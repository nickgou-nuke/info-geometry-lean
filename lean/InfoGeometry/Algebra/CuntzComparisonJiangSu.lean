import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzGrothendieckCone

/-!
# Cuntz Comparison and Abstract Ordered-Monoid States

This module formalizes conditional comparison results for abstract ordered commutative
monoids and normalized additive state functionals. It does not formalize analytic
quasitraces or characterize Jiang-Su ($\mathcal{Z}$) absorption.

It builds directly on the repository owner `InfoGeometry.Algebra.CuntzGrothendieckCone`.

Given an ordered commutative additive monoid $(S, +, \le)$ equipped with an order unit $u$
(representing the Cuntz semigroup $Cu(A)$ or $W(A)$ of a C*-algebra):

1. **Normalized State Functional**: An additive, order-preserving functional
   $\tau : S \to \mathbb{R}$ normalized such that $\tau(u) = 1$.
2. **Grothendieck Cone Projection**: Stable algebraic domination is characterized by
   membership in `grothendieckCone S`.
3. **Strict Comparison** (`HasStrictComparison`): Whenever $\tau(a) < \tau(b)$ for all
   normalized states $\tau$, $[b] - [a]$ lies in `grothendieckCone S`.
4. **Almost Unperforation** (`IsAlmostUnperforated`): The standard order condition
   $(n+1)a \le nb \Rightarrow a \le b$ implies stable algebraic domination.
5. **Order-unit Positivity**: In any non-empty state space, the order unit is
   strictly positive and cannot be dominated by zero.
-/

namespace InfoGeometry.Algebra.CuntzComparison

open _root_.Algebra
open InfoGeometry.Algebra.CuntzGrothendieck

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

/-- A normalized additive positive state functional on an ordered monoid `S` with order unit `u`.

This is an abstract state functional; it does not assert the additional analytic
properties of a C*-algebraic quasitrace. -/
structure CuntzState (u : S) where
  toFun : S → ℝ
  map_add' : ∀ a b, toFun (a + b) = toFun a + toFun b
  monotone' : ∀ a b, a ≤ b → toFun a ≤ toFun b
  nonneg' : ∀ a, 0 ≤ toFun a
  normalized' : toFun u = 1

namespace CuntzState

variable {u : S} (τ : CuntzState u)

instance : CoeFun (CuntzState u) (fun _ => S → ℝ) := ⟨toFun⟩

@[simp] theorem map_add (a b : S) : τ (a + b) = τ a + τ b := τ.map_add' a b
theorem monotone {a b : S} (h : a ≤ b) : τ a ≤ τ b := τ.monotone' a b h
theorem nonneg (a : S) : 0 ≤ τ a := τ.nonneg' a
@[simp] theorem normalized : τ u = 1 := τ.normalized'

@[simp] theorem map_zero : τ 0 = 0 := by
  have h : τ (0 + 0) = τ 0 + τ 0 := τ.map_add 0 0
  rw [add_zero] at h
  linarith

@[simp] theorem map_nsmul (n : ℕ) (a : S) : τ (n • a) = n • τ a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, map_add, ih, succ_nsmul]

/-- A Cuntz state respects stable monoid equality. -/
theorem map_eq_of_stable_eq {a b : S} (h : ∃ c : S, a + c = b + c) : τ a = τ b := by
  rcases h with ⟨c, hc⟩
  have h1 : τ (a + c) = τ (b + c) := by rw [hc]
  simp only [map_add] at h1
  linarith

/-- A Cuntz state respects stable monoid domination. -/
theorem le_of_stable_le {a b : S} (h : ∃ c : S, a + c ≤ b + c) : τ a ≤ τ b := by
  rcases h with ⟨c, hc⟩
  have h1 : τ (a + c) ≤ τ (b + c) := τ.monotone hc
  simp only [map_add] at h1
  linarith

end CuntzState

/-- Abstract strict comparison property for the state functionals defined here.
This is an explicit hypothesis on `(S, u)`, not a theorem about C*-algebras. -/
def HasStrictComparison (u : S) : Prop :=
  ∀ a b : S, (∀ τ : CuntzState u, τ a < τ b) →
    GrothendieckAddGroup.of b - GrothendieckAddGroup.of a ∈ (grothendieckCone (S := S))

/-- Under strict comparison, state domination implies membership in the Grothendieck cone. -/
theorem strict_comparison_mem_cone {u : S} (hsc : HasStrictComparison u)
    (a b : S) (hdom : ∀ τ : CuntzState u, τ a < τ b) :
    GrothendieckAddGroup.of b - GrothendieckAddGroup.of a ∈ (grothendieckCone (S := S)) :=
  hsc a b hdom

/-- Under strict comparison, state domination implies stable algebraic domination. -/
theorem strict_comparison_stable_domination {u : S} (hsc : HasStrictComparison u)
    (a b : S) (hdom : ∀ τ : CuntzState u, τ a < τ b) :
    ∃ c : S, a + c ≤ b + c := by
  have hcone := strict_comparison_mem_cone hsc a b hdom
  exact (grothendieck_mem_cone_iff a b).mp hcone

/-- **Almost Unperforated Ordered Monoid**: if `(n + 1) • a ≤ n • b`, then `a ≤ b`.

This order-theoretic condition alone does not characterize Jiang-Su absorption. -/
def IsAlmostUnperforated : Prop :=
  ∀ (n : ℕ) (a b : S), (n + 1) • a ≤ n • b → a ≤ b

/-- Almost unperforation gives stable domination with zero as stabilizing summand. -/
theorem almost_unperforated_stable_domination (hau : IsAlmostUnperforated (S := S))
    (n : ℕ) (a b : S) (hscale : (n + 1) • a ≤ n • b) :
    ∃ c : S, a + c ≤ b + c := by
  refine ⟨0, ?_⟩
  simpa using hau n a b hscale

/-- Almost unperforation places the Grothendieck difference in the positive cone. -/
theorem almost_unperforated_mem_cone (hau : IsAlmostUnperforated (S := S))
    (n : ℕ) (a b : S) (hscale : (n + 1) • a ≤ n • b) :
    GrothendieckAddGroup.of b - GrothendieckAddGroup.of a ∈ (grothendieckCone (S := S)) := by
  have hstable := almost_unperforated_stable_domination hau n a b hscale
  exact (grothendieck_mem_cone_iff a b).mpr hstable

/-- A normalized state rules out strict domination of the order unit by zero. -/
theorem normalized_state_order_unit_positive {u : S} (τ : CuntzState u) :
    ¬ (∀ τ' : CuntzState u, τ' u < τ' 0) := by
  intro hcontra
  have h_val := hcontra τ
  have hu : τ u = 1 := τ.normalized
  have hz : τ 0 = 0 := τ.map_zero
  rw [hu, hz] at h_val
  linarith

end InfoGeometry.Algebra.CuntzComparison
