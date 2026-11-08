import InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Reciprocal exponential coordinates for the circular hyperbolic flow

This owner records the finite algebraic part of the logarithmic/projective
picture.  The parameter `t` is a real flow parameter; no compactification by
`±∞`, projective topology, or physical-time interpretation is asserted.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge

def reciprocalExponentialPair (t : ℝ) : ℝ × ℝ :=
  (Real.exp t, Real.exp (-t))

@[simp] theorem reciprocalExponentialPair_fst (t : ℝ) :
    (reciprocalExponentialPair t).1 = Real.exp t := rfl

@[simp] theorem reciprocalExponentialPair_snd (t : ℝ) :
    (reciprocalExponentialPair t).2 = Real.exp (-t) := rfl

theorem reciprocalExponentialPair_product (t : ℝ) :
    (reciprocalExponentialPair t).1 *
        (reciprocalExponentialPair t).2 = 1 := by
  simp only [reciprocalExponentialPair]
  rw [← Real.exp_add]
  simp

theorem reciprocalExponentialPair_involution (t : ℝ) :
    reciprocalExponentialPair (-t) =
      ((reciprocalExponentialPair t).2,
        (reciprocalExponentialPair t).1) := by
  apply Prod.ext <;> simp [reciprocalExponentialPair]

theorem reciprocalExponentialPair_zero :
    reciprocalExponentialPair 0 = (1, 1) := by
  simp [reciprocalExponentialPair]

theorem reciprocalExponentialPair_add (s t : ℝ) :
    reciprocalExponentialPair (s + t) =
      ((reciprocalExponentialPair s).1 *
          (reciprocalExponentialPair t).1,
       (reciprocalExponentialPair s).2 *
          (reciprocalExponentialPair t).2) := by
  apply Prod.ext
  · simp [reciprocalExponentialPair, Real.exp_add]
  · change Real.exp (-(s + t)) = Real.exp (-s) * Real.exp (-t)
    rw [neg_add, Real.exp_add]

theorem reciprocalExponentialPair_eq_one_iff {t : ℝ} :
    reciprocalExponentialPair t = (1, 1) ↔ t = 0 := by
  constructor
  · intro h
    have h₁ : Real.exp t = 1 := by
      simpa [reciprocalExponentialPair] using congrArg Prod.fst h
    exact (Real.exp_eq_one_iff t).mp h₁
  · intro ht
    subst t
    exact reciprocalExponentialPair_zero

theorem positiveLog_exp_pair (t : ℝ) :
    (Real.log (Real.exp t), Real.log (Real.exp (-t))) = (t, -t) := by
  simp

theorem exp_log_positive_pair {z : ℝ} (hz : 0 < z) :
    reciprocalExponentialPair (Real.log z) = (z, z⁻¹) := by
  apply Prod.ext
  · simp [reciprocalExponentialPair, Real.exp_log hz]
  · rw [reciprocalExponentialPair]
    rw [Real.exp_neg, Real.exp_log hz]

theorem reciprocalExponentialPair_cosh_sinh (t : ℝ) :
    (Real.cosh t, Real.sinh t) =
      (((reciprocalExponentialPair t).1 +
          (reciprocalExponentialPair t).2) / 2,
        ((reciprocalExponentialPair t).1 -
          (reciprocalExponentialPair t).2) / 2) := by
  simp only [reciprocalExponentialPair]
  rw [Real.cosh_eq, Real.sinh_eq]

@[simp] theorem reciprocalExponentialPair_cosh_sinh_zero :
    (Real.cosh 0, Real.sinh 0) = (1, 0) := by
  simp

theorem reciprocal_exponential_channel_invariant
    (xPlus xMinus t : ℝ) :
    (Real.exp t * xPlus) * (Real.exp (-t) * xMinus) = xPlus * xMinus := by
  calc
    (Real.exp t * xPlus) * (Real.exp (-t) * xMinus) =
        (Real.exp t * Real.exp (-t)) * (xPlus * xMinus) := by ring
    _ = xPlus * xMinus := by
      rw [← Real.exp_add]
      simp

end InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge
