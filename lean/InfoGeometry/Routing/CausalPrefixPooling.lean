/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Finite-set pooling and prefix noninterference

Finite sets represent allowed tokens/chunks; an empty set has zero pooled
output. No finite sentinel stands for a masked logarithm. These are exact
real formulas, not a certification of floating-point code or its domain checks.
The derivative theorem concerns a constant future-coordinate partial map;
it does not require differentiability with respect to past coordinates.
-/
noncomputable section
namespace InfoGeometry.Routing.CausalPrefixPooling
open scoped BigOperators

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Allowed-set exponential partition, including the empty-set case. -/
def partition (S : Finset C) (m : C → ℝ) : ℝ :=
  ∑ s ∈ S, Real.exp (m s)

/-- Masked probability weights; normalization needs a nonempty allowed set. -/
def weight (S : Finset C) (m : C → ℝ) (s : C) : ℝ :=
  if s ∈ S then Real.exp (m s) / partition S m else 0

/-- Coordinatewise pooling, sufficient for matrix-valued features. -/
def pool (S : Finset C) (m X : C → ℝ) : ℝ :=
  ∑ s, weight S m s * X s

theorem partition_pos (S : Finset C) (hS : S.Nonempty) (m : C → ℝ) :
    0 < partition S m := by
  exact Finset.sum_pos (fun s _ => Real.exp_pos (m s)) hS

theorem weight_nonneg (S : Finset C) (m : C → ℝ) (s : C) :
    0 ≤ weight S m s := by
  unfold weight
  split_ifs
  · exact div_nonneg (Real.exp_pos _).le
      (Finset.sum_nonneg (fun r _ => (Real.exp_pos (m r)).le))
  · exact le_rfl

theorem weight_sum_one (S : Finset C) (hS : S.Nonempty) (m : C → ℝ) :
    ∑ s, weight S m s = 1 := by
  simp only [weight, ← Finset.sum_filter]
  have he : Finset.univ.filter (fun s => s ∈ S) = S := by
    ext s
    simp
  rw [he]
  rw [← Finset.sum_div]
  exact div_self (partition_pos S hS m).ne'

theorem weight_of_not_mem (S : Finset C) (m : C → ℝ) {s : C} (hs : s ∉ S) :
    weight S m s = 0 := by simp [weight, hs]

theorem pool_empty (m X : C → ℝ) : pool ∅ m X = 0 := by
  simp [pool, weight]

theorem partition_congr (S : Finset C) {m n : C → ℝ}
    (h : Set.EqOn m n (S : Set C)) : partition S m = partition S n := by
  exact Finset.sum_congr rfl (fun s hs => congrArg Real.exp (h hs))

theorem weight_congr (S : Finset C) {m n : C → ℝ}
    (h : Set.EqOn m n (S : Set C)) (s : C) : weight S m s = weight S n s := by
  unfold weight
  by_cases hs : s ∈ S
  · rw [if_pos hs, if_pos hs, h hs, partition_congr S h]
  · rw [if_neg hs, if_neg hs]

theorem pool_congr (S : Finset C) {m n X Y : C → ℝ}
    (hm : Set.EqOn m n (S : Set C)) (hX : Set.EqOn X Y (S : Set C)) :
    pool S m X = pool S n Y := by
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ S
  · rw [weight_congr S hm s, hX hs]
  · rw [weight_of_not_mem S m hs, weight_of_not_mem S n hs, zero_mul, zero_mul]

/-- Algebra behind streaming union of two nonempty weighted pools. -/
theorem merge_barycenters (a b u v : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a / (a+b)) * (u/a) + (b / (a+b)) * (v/b) = (u+v)/(a+b) := by
  by_cases hz : a+b = 0
  · simp [hz]
  · field_simp [ha, hb, hz]
    <;> ring

/-- Nested chunk pooling equals pooling all allowed tokens, with no independence
assumption. The positive masses are explicit, not an assumed output equality. -/
theorem hierarchical_pool {L : Type*} [Fintype L]
    (S : Finset C) (w : C → L → ℝ) (X : C → L → ℝ)
    (hmass : ∀ s ∈ S, (∑ i, w s i) ≠ 0)
    (htotal : (∑ s ∈ S, ∑ i, w s i) ≠ 0) :
    (∑ s ∈ S, ((∑ i, w s i) / (∑ r ∈ S, ∑ i, w r i)) *
      (∑ i, (w s i / (∑ j, w s j)) * X s i)) =
      (∑ s ∈ S, ∑ i, w s i * X s i) / (∑ s ∈ S, ∑ i, w s i) := by
  conv_rhs => rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hmass s hs, htotal]
  <;> ring

section Order
variable [LinearOrder C]

/-- Inclusive prefix. Strictly-past prefixes use `Finset.univ.filter (· < t)`
and may be empty; the finite-set statements above handle that case. -/
def prefixSet (t : C) : Finset C := Finset.univ.filter (fun s => s ≤ t)

theorem prefix_nonempty (t : C) : (prefixSet t).Nonempty := by
  exact ⟨t, by simp [prefixSet]⟩

theorem prefix_weight_future (m : C → ℝ) {t s : C} (h : t < s) :
    weight (prefixSet t) m s = 0 := by
  apply weight_of_not_mem
  simp [prefixSet, not_le.mpr h]

theorem prefix_pool_congr {m n X Y : C → ℝ} (t : C)
    (hm : Set.EqOn m n (Set.Iic t)) (hX : Set.EqOn X Y (Set.Iic t)) :
    pool (prefixSet t) m X = pool (prefixSet t) n Y := by
  apply pool_congr
  · intro s hs
    exact hm (Finset.mem_filter.mp hs).2
  · intro s hs
    exact hX (Finset.mem_filter.mp hs).2

/-- Set-theoretic locality composes with arbitrary per-prefix processing. -/
theorem local_postprocess {E F G : Type*} (t : C) (f : (C → E) → F)
    (h : ∀ x y, Set.EqOn x y (Set.Iic t) → f x = f y) (g : F → G)
    (x y : C → E) (hxy : Set.EqOn x y (Set.Iic t)) :
    g (f x) = g (f y) := congrArg g (h x y hxy)

/-- Native `Function.update` does not alter any earlier input coordinate. -/
theorem update_future_eqOn {E : Type*} (x : C → E) {t s : C} (h : t < s) (v : E) :
    Set.EqOn (Function.update x s v) x (Set.Iic t) := by
  intro r hr
  have hne : r ≠ s := ne_of_lt (lt_of_le_of_lt hr h)
  simp [Function.update, hne, Ne.symm hne]

/-- Exact noninterference gives a zero future Fréchet derivative and zero VJP.
This statement neither assumes nor concludes a derivative in other directions. -/
theorem future_derivative_and_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (t : C) (f : (C → E) → F)
    (hlocal : ∀ x y, Set.EqOn x y (Set.Iic t) → f x = f y)
    (x : C → E) {s : C} (hfuture : t < s) (ell : F →L[ℝ] ℝ) :
    HasFDerivAt (fun v => f (Function.update x s v)) (0 : E →L[ℝ] F) (x s) ∧
    HasFDerivAt (fun v => ell (f (Function.update x s v)))
      (0 : E →L[ℝ] ℝ) (x s) ∧
    ell.comp (0 : E →L[ℝ] F) = 0 := by
  have heq : (fun v => f (Function.update x s v)) = fun _ : E => f x := by
    funext v
    exact hlocal _ _ (update_future_eqOn x hfuture v)
  have hd : HasFDerivAt (fun v => f (Function.update x s v))
      (0 : E →L[ℝ] F) (x s) := by
    rw [heq]
    exact hasFDerivAt_const (𝕜 := ℝ) (f x) (x s)
  refine ⟨hd, ?_, by simp⟩
  have heq_scalar : (fun v => ell (f (Function.update x s v))) =
      fun _ : E => ell (f x) := by
    funext v
    exact congrArg ell (congrFun heq v)
  rw [heq_scalar]
  exact hasFDerivAt_const (𝕜 := ℝ) (ell (f x)) (x s)

end Order
end InfoGeometry.Routing.CausalPrefixPooling
