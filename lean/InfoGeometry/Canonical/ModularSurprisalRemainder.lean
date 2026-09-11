import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Linarith

noncomputable section

/-!
# Scalar modular-surprisal exponential remainder

This owner records the scalar theorem behind the operator expression
`exp (-β K) - 1 + β K`.  It deliberately does not claim a functional-calculus
result for general operators.
-/

namespace InfoGeometry.Canonical.ModularSurprisalRemainder

/-- The scalar exponential remainder after removing its affine part. -/
def remainder (β k : ℝ) : ℝ := Real.exp (-β * k) - 1 + β * k

/-- The exponential remainder is nonnegative. -/
theorem remainder_nonneg (β k : ℝ) : 0 ≤ remainder β k := by
  unfold remainder
  have h := Real.add_one_le_exp (-β * k)
  linarith

/-- Vanishing of the remainder is equivalent to vanishing of the exponent. -/
theorem remainder_eq_zero_iff (β k : ℝ) :
    remainder β k = 0 ↔ β * k = 0 := by
  constructor
  · intro h
    by_contra hne
    have harg : -β * k ≠ 0 := by
      intro hz
      apply hne
      linarith
    have hle := Real.add_one_lt_exp harg
    unfold remainder at h
    linarith
  · intro h
    unfold remainder
    simp [h]

end InfoGeometry.Canonical.ModularSurprisalRemainder
