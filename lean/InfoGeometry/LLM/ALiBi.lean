import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.LLM

/-! # ALiBi as a relative score kernel

This file records the score-level part of ALiBi.  It is deliberately
independent of a particular attention implementation: `dot` is the
unmodified query-key score, while `p` is the head-specific slope.
-/

def alibiScore {Q : Type*} (dot : Q → Q → ℝ) (p : ℝ)
    (q k : Q) (t s : ℝ) : ℝ :=
  dot q k - p * (t - s)

theorem alibiScore_translation_invariant {Q : Type*} (dot : Q → Q → ℝ)
    (p : ℝ) (q k : Q) (t s a : ℝ) :
    alibiScore dot p q k (t + a) (s + a) = alibiScore dot p q k t s := by
  simp [alibiScore]

theorem alibiScore_same_time {Q : Type*} (dot : Q → Q → ℝ)
    (p : ℝ) (q k : Q) (t : ℝ) :
    alibiScore dot p q k t t = dot q k := by
  simp [alibiScore]

/-- The linear relative-position term is a rank-two bilinear factorization.

The two auxiliary coordinates are not asserted to be part of the model's
learned content; they only realize the score bias algebraically.
-/
def alibiAugmentedScore {Q : Type*} (dot : Q → Q → ℝ) (p : ℝ)
    (q k : Q) (t s : ℝ) : ℝ :=
  dot q k + (-p * t) * 1 + 1 * (p * s)

theorem alibiAugmentedScore_eq_alibiScore {Q : Type*} (dot : Q → Q → ℝ)
    (p : ℝ) (q k : Q) (t s : ℝ) :
    alibiAugmentedScore dot p q k t s = alibiScore dot p q k t s := by
  simp [alibiAugmentedScore, alibiScore]
  ring

theorem alibiAugmentedScore_translation_invariant {Q : Type*}
    (dot : Q → Q → ℝ) (p : ℝ) (q k : Q) (t s a : ℝ) :
    alibiAugmentedScore dot p q k (t + a) (s + a)
      = alibiAugmentedScore dot p q k t s := by
  rw [alibiAugmentedScore_eq_alibiScore,
    alibiAugmentedScore_eq_alibiScore,
    alibiScore_translation_invariant]

end InfoGeometry.LLM
