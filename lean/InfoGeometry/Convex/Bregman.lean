import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bregman Divergence

Core Bregman divergence definitions and theorems.

## Main results
- `bregmanDiv`
- `bregmanThreePoint`
- `bregmanThreePoint_sub`
- `bregmanPythagoreanIneq_of_crossTerm_nonneg`

-/

namespace InfoGeometry

-- Bregman divergence for a convex function F
noncomputable def bregmanDiv (F : ℝ → ℝ) (x y : ℝ) : ℝ :=
  F x - F y - deriv F y * (x - y)

/-- Three-point identity for Bregman divergence. -/
lemma bregmanThreePoint (F : ℝ → ℝ) (x y z : ℝ) :
  bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z + (deriv F y - deriv F z) * (x - y) :=
by
  simp [bregmanDiv]
  ring

/-- Rearranged three-point identity isolating the cross term. -/
lemma bregmanThreePoint_sub (F : ℝ → ℝ) (x y z : ℝ) :
  bregmanDiv F x z - bregmanDiv F x y - bregmanDiv F y z
    = (deriv F y - deriv F z) * (x - y) := by
  have h := bregmanThreePoint F x y z
  linarith

/-- Conditional Bregman Pythagorean inequality from a nonnegative cross term.
Deriving the cross-term sign from convexity/projection assumptions is separate. -/
lemma bregmanPythagoreanIneq_of_crossTerm_nonneg
    (F : ℝ → ℝ) (x y z : ℝ)
    (hproj : 0 ≤ (deriv F y - deriv F z) * (x - y)) :
    bregmanDiv F x z ≥ bregmanDiv F x y + bregmanDiv F y z :=
by
  have hdecomp := bregmanThreePoint F x y z
  linarith [hdecomp, hproj]

/-- Backward-compatible alias for
`bregmanPythagoreanIneq_of_crossTerm_nonneg`. -/
lemma bregmanPythagoreanIneq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hproj : 0 ≤ (deriv F y - deriv F z) * (x - y)) :
    bregmanDiv F x z ≥ bregmanDiv F x y + bregmanDiv F y z :=
  bregmanPythagoreanIneq_of_crossTerm_nonneg F x y z hproj

end InfoGeometry
