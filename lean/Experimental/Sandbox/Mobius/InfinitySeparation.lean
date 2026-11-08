import Experimental.Sandbox.Mobius.InfinityCases
import Experimental.Sandbox.Mobius.PoleCases

namespace Experimental.Sandbox.Mobius

lemma fractionalLinear_ne_infinity_image_of_den_ne_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ)
    (hc : M.c ≠ 0) (hden : M.c * z + M.d ≠ 0) :
    (M.a * z + M.b) / (M.c * z + M.d) ≠ M.a / M.c := by
  intro h
  have hcz : z * M.c + M.d ≠ 0 := by simpa [mul_comm] using hden
  field_simp [hc, hden, hcz] at h
  have hbc : M.b * M.c = M.a * M.d := by
    calc
      M.b * M.c = (M.a * z + M.b) * M.c - M.a * z * M.c := by ring
      _ = M.a * (z * M.c + M.d) - M.a * z * M.c := by rw [h]
      _ = M.a * M.d := by ring
  have hzero : M.a * M.d - M.b * M.c = 0 := by
    rw [sub_eq_zero]
    exact hbc.symm
  exact M.det_ne_zero hzero

lemma eval_some_ne_eval_none_of_c_ne_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ)
    (hc : M.c ≠ 0) (hden : M.c * z + M.d ≠ 0) :
    M.eval (some z) ≠ M.eval none := by
  rw [eval_some_eq_fractional_of_den_ne_zero M z hden,
      eval_none_eq_some_of_c_ne_zero M hc]
  intro h
  injection h with hfrac
  exact fractionalLinear_ne_infinity_image_of_den_ne_zero M z hc hden hfrac

lemma finite_image_value_ne_infinity_image_value
    (M : InfoGeometry.MobiusTransform) (z w : ℂ)
    (hc : M.c ≠ 0) (hden : M.c * z + M.d ≠ 0)
    (hz : M.eval (some z) = some w) :
    w ≠ M.a / M.c := by
  rw [eval_some_eq_fractional_of_den_ne_zero M z hden] at hz
  injection hz with hw
  subst w
  exact fractionalLinear_ne_infinity_image_of_den_ne_zero M z hc hden

lemma no_common_finite_and_infinity_image
    (M : InfoGeometry.MobiusTransform) (z winf : ℂ)
    (hc : M.c ≠ 0) (hden : M.c * z + M.d ≠ 0)
    (hz : M.eval (some z) = some winf) (hinf : M.eval none = some winf) :
    False := by
  have hvalue := eval_none_some_value_unique M winf hinf
  exact finite_image_value_ne_infinity_image_value M z winf hc hden hz hvalue

end Experimental.Sandbox.Mobius
