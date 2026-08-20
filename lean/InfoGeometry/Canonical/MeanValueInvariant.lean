import Mathlib.Analysis.Calculus.MeanValue

/-!
# Zero derivative and global invariance

This file isolates the exact mean-value-theorem statement used by
interaction-picture arguments: an everywhere Fréchet-differentiable map on a
real line whose derivative is identically zero is constant.

It does not construct a flow or identify a statistical expectation with the
mean-value theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.MeanValueInvariant

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An everywhere-zero Fréchet derivative forces equality at any two times. -/
theorem eq_of_hasFDerivAt_zero
    {F : ℝ → E}
    (hF : ∀ t : ℝ,
      HasFDerivAt F (0 : ℝ →L[ℝ] E) t)
    (s t : ℝ) :
    F s = F t := by
  apply is_const_of_fderiv_eq_zero
  · intro x
    exact (hF x).differentiableAt
  · intro x
    exact (hF x).fderiv

/-- Function-level form of the same invariant statement. -/
theorem eq_const_of_hasFDerivAt_zero
    {F : ℝ → E}
    (hF : ∀ t : ℝ,
      HasFDerivAt F (0 : ℝ →L[ℝ] E) t)
    (t₀ : ℝ) :
    F = fun _ => F t₀ := by
  funext t
  exact eq_of_hasFDerivAt_zero hF t t₀

/-- A zero derivative identifies the value at every time with the value at zero. -/
theorem eq_zero_time_of_hasFDerivAt_zero
    {F : ℝ → E}
    (hF : ∀ t : ℝ,
      HasFDerivAt F (0 : ℝ →L[ℝ] E) t)
    (t : ℝ) :
    F t = F 0 :=
  eq_of_hasFDerivAt_zero hF t 0

end InfoGeometry.Canonical.MeanValueInvariant

end noncomputable section
