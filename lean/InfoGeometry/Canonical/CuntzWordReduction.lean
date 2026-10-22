/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Basic
import InfoGeometry.Canonical.CuntzNIsometries

open BigOperators

namespace CuntzAlgebra

variable {n : ℕ} {A : Type*} [Ring A] [StarRing A]

/-- Monomial isometry corresponding to a multi-index word w : List (Fin n) -/
def wordS (c : CuntzIsometries n A) : List (Fin n) → A
  | [] => 1
  | i :: w => c.S i * wordS c w

/-- Adjoint of monomial isometry corresponding to a word w : List (Fin n) -/
def wordSStar (c : CuntzIsometries n A) : List (Fin n) → A
  | [] => 1
  | i :: w => wordSStar c w * star (c.S i)

/-- Multiplicative homomorphism for concatenated words: S_(w ++ v) = S_w * S_v -/
theorem wordS_append (c : CuntzIsometries n A) (w v : List (Fin n)) :
    wordS c (w ++ v) = wordS c w * wordS c v := by
  induction w with
  | nil =>
    dsimp [wordS]
    rw [one_mul]
  | cons i w ih =>
    dsimp [wordS]
    rw [ih, mul_assoc]

/-- 🏆 THEOREM 1: Matching Head Index Cancellation (S_(i::w1)* S_(i::w2) = S_w1* S_w2) -/
theorem word_reduction_head_match (c : CuntzIsometries n A) (i : Fin n) (w1 w2 : List (Fin n)) :
    wordSStar c (i :: w1) * wordS c (i :: w2) = wordSStar c w1 * wordS c w2 := by
  dsimp [wordSStar, wordS]
  calc (wordSStar c w1 * star (c.S i)) * (c.S i * wordS c w2)
    _ = wordSStar c w1 * (star (c.S i) * c.S i) * wordS c w2 := by simp [mul_assoc]
    _ = wordSStar c w1 * 1 * wordS c w2 := by simp [isometry_delta]
    _ = wordSStar c w1 * wordS c w2 := by rw [mul_one]

/-- 🏆 THEOREM 2: Divergent Head Index Mismatch (i ≠ j ⟹ S_(i::w1)* S_(j::w2) = 0) -/
theorem word_reduction_head_mismatch (c : CuntzIsometries n A) {i j : Fin n} (h : i ≠ j)
    (w1 w2 : List (Fin n)) :
    wordSStar c (i :: w1) * wordS c (j :: w2) = 0 := by
  dsimp [wordSStar, wordS]
  calc (wordSStar c w1 * star (c.S i)) * (c.S j * wordS c w2)
    _ = wordSStar c w1 * (star (c.S i) * c.S j) * wordS c w2 := by simp [mul_assoc]
    _ = wordSStar c w1 * 0 * wordS c w2 := by
      rw [show star (c.S i) * c.S j = 0 by simpa [h] using isometry_delta c i j]
    _ = 0 := by rw [mul_zero, zero_mul]

/-- 🏆 THEOREM 3: Right Prefix Reduction (S_w* S_(w ++ v) = S_v) -/
theorem word_reduction_prefix_right (c : CuntzIsometries n A) (w v : List (Fin n)) :
    wordSStar c w * wordS c (w ++ v) = wordS c v := by
  induction w with
  | nil =>
    dsimp [wordSStar, wordS]
    rw [one_mul]
  | cons i w ih =>
    rw [List.cons_append]
    rw [word_reduction_head_match]
    exact ih

/-- The adjoint word reverses concatenation order. -/
theorem wordSStar_append (c : CuntzIsometries n A) (w v : List (Fin n)) :
    wordSStar c (w ++ v) = wordSStar c v * wordSStar c w := by
  induction w with
  | nil => simp [wordSStar]
  | cons i w ih =>
      rw [List.cons_append]
      simp only [wordSStar]
      rw [ih]
      simp [mul_assoc]

/-- 🏆 THEOREM 4: Left Prefix Reduction (S_(w ++ v)* S_w = S_v*) -/
theorem word_reduction_prefix_left (c : CuntzIsometries n A) (w v : List (Fin n)) :
    wordSStar c (w ++ v) * wordS c w = wordSStar c v := by
  induction w with
  | nil =>
    dsimp [wordSStar, wordS]
    rw [mul_one]
  | cons i w ih =>
    have h_app : (i :: w) ++ v = i :: (w ++ v) := rfl
    rw [h_app]
    rw [word_reduction_head_match]
    exact ih

/-- Incomparable words have orthogonal initial spaces: after their first
mismatching letter, the Cuntz relations force the product to vanish. -/
theorem word_reduction_zero_of_prefix_incomparable
    (c : CuntzIsometries n A) (v x : List (Fin n))
    (hvx : ¬ ∃ t, x = v ++ t) (hxv : ¬ ∃ t, v = x ++ t) :
    wordSStar c v * wordS c x = 0 := by
  revert hvx hxv
  induction v generalizing x with
  | nil =>
      intro hvx hxv
      exact (hvx ⟨x, by simp⟩).elim
  | cons i v ih =>
      cases x with
      | nil =>
          intro hvx hxv
          exact (hxv ⟨i :: v, by simp⟩).elim
      | cons j x =>
          intro hvx hxv
          by_cases hij : i = j
          · subst j
            have hvx' : ¬ ∃ t, x = v ++ t := by
              intro h
              rcases h with ⟨t, ht⟩
              exact hvx ⟨t, by simp [ht]⟩
            have hxv' : ¬ ∃ t, v = x ++ t := by
              intro h
              rcases h with ⟨t, ht⟩
              exact hxv ⟨t, by simp [ht]⟩
            rw [word_reduction_head_match]
            exact ih x hvx' hxv'
          · exact word_reduction_head_mismatch c hij v x

/-- Complete prefix-cancellation law for two Cuntz words.  If one word is a
prefix of the other, the unmatched suffix survives; if neither is a prefix,
the product is zero. -/
theorem word_reduction_prefix_cases
    (c : CuntzIsometries n A) (v x : List (Fin n)) :
    (∃ t, x = v ++ t ∧
      wordSStar c v * wordS c x = wordS c t) ∨
    (∃ t, v = x ++ t ∧
      wordSStar c v * wordS c x = wordSStar c t) ∨
    ((¬ ∃ t, x = v ++ t) ∧ (¬ ∃ t, v = x ++ t) ∧
      wordSStar c v * wordS c x = 0) := by
  classical
  by_cases hvx : ∃ t, x = v ++ t
  · rcases hvx with ⟨t, rfl⟩
    left
    exact ⟨t, rfl, word_reduction_prefix_right c v t⟩
  · by_cases hxv : ∃ t, v = x ++ t
    · rcases hxv with ⟨t, rfl⟩
      right
      left
      exact ⟨t, rfl, word_reduction_prefix_left c x t⟩
    · right
      right
      exact ⟨hvx, hxv,
        word_reduction_zero_of_prefix_incomparable c v x hvx hxv⟩

/-- 🏆 THEOREM 5: Exact Word Isometry (S_w* S_w = 1) -/
theorem word_reduction_exact (c : CuntzIsometries n A) (w : List (Fin n)) :
    wordSStar c w * wordS c w = 1 := by
  have h := word_reduction_prefix_right c w []
  rw [List.append_nil] at h
  exact h

end CuntzAlgebra
