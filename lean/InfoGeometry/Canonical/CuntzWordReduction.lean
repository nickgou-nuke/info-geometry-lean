import Mathlib.Algebra.Star.Basic
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
    _ = wordSStar c w1 * 1 * wordS c w2 := by rw [c.h_isometry i]
    _ = wordSStar c w1 * wordS c w2 := by rw [mul_one]

/-- 🏆 THEOREM 2: Divergent Head Index Mismatch (i ≠ j ⟹ S_(i::w1)* S_(j::w2) = 0) -/
theorem word_reduction_head_mismatch (c : CuntzIsometries n A) {i j : Fin n} (h : i ≠ j)
    (w1 w2 : List (Fin n)) :
    wordSStar c (i :: w1) * wordS c (j :: w2) = 0 := by
  dsimp [wordSStar, wordS]
  calc (wordSStar c w1 * star (c.S i)) * (c.S j * wordS c w2)
    _ = wordSStar c w1 * (star (c.S i) * c.S j) * wordS c w2 := by simp [mul_assoc]
    _ = wordSStar c w1 * 0 * wordS c w2 := by rw [c.h_ortho i j h]
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

/-- 🏆 THEOREM 5: Exact Word Isometry (S_w* S_w = 1) -/
theorem word_reduction_exact (c : CuntzIsometries n A) (w : List (Fin n)) :
    wordSStar c w * wordS c w = 1 := by
  have h := word_reduction_prefix_right c w []
  rw [List.append_nil] at h
  exact h

end CuntzAlgebra
