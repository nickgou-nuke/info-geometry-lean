import Experimental.Sandbox.Mobius.AffineCase
import Experimental.Sandbox.Mobius.FiniteInjective

namespace Experimental.Sandbox.Mobius

lemma a_ne_zero_of_c_eq_zero
    (M : InfoGeometry.MobiusTransform) (hc : M.c = 0) :
    M.a ≠ 0 := by
  intro ha
  apply M.det_ne_zero
  rw [hc, ha]
  ring

lemma slope_ne_zero_of_c_eq_zero
    (M : InfoGeometry.MobiusTransform) (hc : M.c = 0) :
    M.a / M.d ≠ 0 := by
  exact div_ne_zero (a_ne_zero_of_c_eq_zero M hc) (d_ne_zero_of_c_eq_zero M hc)

lemma affine_slope_intercept_eval_value
    (M : InfoGeometry.MobiusTransform) (z w : ℂ) (hc : M.c = 0)
    (h : M.eval (some z) = some w) :
    w = (M.a / M.d) * z + M.b / M.d := by
  rw [eval_some_eq_slope_intercept_of_c_eq_zero M z hc] at h
  injection h with hw
  exact hw.symm

lemma affine_slope_intercept_injective
    (M : InfoGeometry.MobiusTransform) (z₁ z₂ : ℂ) (hc : M.c = 0) :
    (M.a / M.d) * z₁ + M.b / M.d = (M.a / M.d) * z₂ + M.b / M.d ↔ z₁ = z₂ := by
  constructor
  · intro h
    have hslope := slope_ne_zero_of_c_eq_zero M hc
    have hcancel : (M.a / M.d) * z₁ = (M.a / M.d) * z₂ := by
      exact add_right_cancel h
    have hmul : (M.a / M.d) * (z₁ - z₂) = 0 := by
      rw [mul_sub, hcancel, sub_self]
    have hdiff : z₁ - z₂ = 0 := (mul_eq_zero.mp hmul).resolve_left hslope
    exact sub_eq_zero.mp hdiff
  · intro h
    subst z₂
    rfl

lemma affine_eval_some_injective_of_c_eq_zero
    (M : InfoGeometry.MobiusTransform) (z₁ z₂ : ℂ) (hc : M.c = 0)
    (h : M.eval (some z₁) = M.eval (some z₂)) :
    z₁ = z₂ := by
  rw [eval_some_eq_slope_intercept_of_c_eq_zero M z₁ hc,
      eval_some_eq_slope_intercept_of_c_eq_zero M z₂ hc] at h
  injection h with hs
  exact (affine_slope_intercept_injective M z₁ z₂ hc).mp hs

end Experimental.Sandbox.Mobius
