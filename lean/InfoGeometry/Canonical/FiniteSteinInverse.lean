/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-!
# Finite Stein inverse

For the map W ↦ W - a W b, nilpotence of either multiplication factor
makes the geometric sum exact. This is a discrete Stein equation, not the
continuous Sylvester equation aW+Wb=X. No commutativity of a,b,X is required.
-/
namespace InfoGeometry.Canonical.FiniteSteinInverse
open scoped BigOperators
variable {R : Type*} [Ring R]

def finiteStein (a b x : R) (k : ℕ) : R :=
  ∑ m ∈ Finset.range k, a ^ m * x * b ^ m

/-- The boundary term is kept explicit, including k=0. -/
theorem telescoping (a b x : R) (k : ℕ) :
    finiteStein a b x k - a * finiteStein a b x k * b =
      x - a ^ k * x * b ^ k := by
  induction k with
  | zero => simp [finiteStein]
  | succ k ih =>
    have hs : finiteStein a b x (k + 1) = finiteStein a b x k + a ^ k * x * b ^ k := by
      simp only [finiteStein, Finset.sum_range_succ]
    rw [hs, mul_add, add_mul]
    have hpow : a * (a ^ k * x * b ^ k) * b = a ^ (k + 1) * x * b ^ (k + 1) := by
      rw [pow_succ' a, pow_succ b]
      simp only [mul_assoc]
    rw [hpow]
    calc
      _ = (finiteStein a b x k - a * finiteStein a b x k * b) +
          a ^ k * x * b ^ k - a ^ (k + 1) * x * b ^ (k + 1) := by abel
      _ = _ := by rw [ih]; abel

/-- Nilpotence of the left factor alone is sufficient. -/
theorem solve_of_left_nilpotent (a b x : R) (k : ℕ) (ha : a ^ k = 0) :
    finiteStein a b x k - a * finiteStein a b x k * b = x := by
  rw [telescoping, ha, zero_mul, zero_mul, sub_zero]

/-- Nilpotence of the right factor alone is sufficient. -/
theorem solve_of_right_nilpotent (a b x : R) (k : ℕ) (hb : b ^ k = 0) :
    finiteStein a b x k - a * finiteStein a b x k * b = x := by
  rw [telescoping, hb, mul_zero, sub_zero]

lemma fixed_point_iterate (a b z : R) (h : z = a * z * b) (k : ℕ) :
    z = a ^ k * z * b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      z = a * z * b := h
      _ = a * (a ^ k * z * b ^ k) * b := by rw [← ih]
      _ = a ^ (k + 1) * z * b ^ (k + 1) := by
        rw [pow_succ' a, pow_succ b]
        simp only [mul_assoc]

/-- Uniqueness is proved algebraically, not inferred from numerical solvability. -/
theorem solution_unique (a b x u v : R) (k : ℕ) (ha : a ^ k = 0)
    (hu : u - a * u * b = x) (hv : v - a * v * b = x) : u = v := by
  have hz : u - v = a * (u - v) * b := by
    apply sub_eq_zero.mp
    calc
      (u - v) - a * (u - v) * b = (u - a * u * b) - (v - a * v * b) := by
        noncomm_ring
      _ = 0 := by rw [hu, hv, sub_self]
  have hh := fixed_point_iterate a b (u - v) hz k
  rw [ha, zero_mul, zero_mul] at hh
  exact sub_eq_zero.mp hh

theorem existsUnique_solution (a b x : R) (k : ℕ) (ha : a ^ k = 0) :
    ∃! w : R, w - a * w * b = x := by
  refine ⟨finiteStein a b x k, solve_of_left_nilpotent a b x k ha, ?_⟩
  intro w hw
  exact solution_unique a b x w (finiteStein a b x k) k ha hw
    (solve_of_left_nilpotent a b x k ha)

/-- The same sum is a left inverse of the Stein map as well. -/
theorem reconstruct (a b w : R) (k : ℕ) (ha : a ^ k = 0) :
    finiteStein a b (w - a * w * b) k = w := by
  apply solution_unique a b (w - a * w * b) _ w k ha
  · exact solve_of_left_nilpotent _ _ _ _ ha
  · rfl

section Star
variable [StarRing R]

/-- The left finite controllability Gramian solves its Stein equation. -/
theorem left_gramian_stein (n : R) (k : ℕ) (hn : n ^ k = 0) :
    finiteStein n (star n) 1 k - n * finiteStein n (star n) 1 k * star n = 1 :=
  solve_of_left_nilpotent _ _ _ _ hn

theorem left_gramian_selfAdjoint (n : R) (k : ℕ) :
    star (finiteStein n (star n) 1 k) = finiteStein n (star n) 1 k := by
  simp only [finiteStein, star_sum, star_mul, star_one, star_pow, star_star, mul_one,
    one_mul]

theorem right_gramian_stein (n : R) (k : ℕ) (hn : n ^ k = 0) :
    finiteStein (star n) n 1 k - star n * finiteStein (star n) n 1 k * n = 1 :=
  solve_of_right_nilpotent _ _ _ _ hn
end Star
end InfoGeometry.Canonical.FiniteSteinInverse
