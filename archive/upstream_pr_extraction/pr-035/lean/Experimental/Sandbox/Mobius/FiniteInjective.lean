import Experimental.Sandbox.Mobius.FiniteCrossRatio

namespace Experimental.Sandbox.Mobius

lemma fractionalLinear_eq_iff
    (M : InfoGeometry.MobiusTransform) (z w : ℂ)
    (hz : M.c * z + M.d ≠ 0) (hw : M.c * w + M.d ≠ 0) :
    (M.a * z + M.b) / (M.c * z + M.d) =
        (M.a * w + M.b) / (M.c * w + M.d) ↔ z = w := by
  constructor
  · intro h
    have hsub :
        (M.a * M.d - M.b * M.c) * (z - w) /
            ((M.c * z + M.d) * (M.c * w + M.d)) = 0 := by
      rw [← fractionalLinear_sub M z w hz hw]
      exact sub_eq_zero.mpr h
    have hden : (M.c * z + M.d) * (M.c * w + M.d) ≠ 0 := mul_ne_zero hz hw
    have hmul : (M.a * M.d - M.b * M.c) * (z - w) = 0 := by
      cases div_eq_zero_iff.mp hsub with
      | inl hnum => exact hnum
      | inr hzero => exact (hden hzero).elim
    have hzw : z - w = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left M.det_ne_zero
    exact sub_eq_zero.mp hzw
  · intro h
    rw [h]

lemma eval_some_injective_of_den_ne_zero
    (M : InfoGeometry.MobiusTransform) (z w : ℂ)
    (hz : M.c * z + M.d ≠ 0) (hw : M.c * w + M.d ≠ 0)
    (h : M.eval (some z) = M.eval (some w)) :
    z = w := by
  rw [eval_some_eq_fractional_of_den_ne_zero M z hz,
      eval_some_eq_fractional_of_den_ne_zero M w hw] at h
  injection h with hfrac
  exact (fractionalLinear_eq_iff M z w hz hw).mp hfrac

lemma eval_some_ne_of_ne_and_den_ne_zero
    (M : InfoGeometry.MobiusTransform) (z w : ℂ)
    (hz : M.c * z + M.d ≠ 0) (hw : M.c * w + M.d ≠ 0)
    (hzw : z ≠ w) :
    M.eval (some z) ≠ M.eval (some w) := by
  intro h
  exact hzw (eval_some_injective_of_den_ne_zero M z w hz hw h)

end Experimental.Sandbox.Mobius
