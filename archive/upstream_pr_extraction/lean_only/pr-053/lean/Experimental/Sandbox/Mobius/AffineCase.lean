import Experimental.Sandbox.Mobius.FiniteCrossRatio

namespace Experimental.Sandbox.Mobius

lemma d_ne_zero_of_c_eq_zero
    (M : InfoGeometry.MobiusTransform) (hc : M.c = 0) :
    M.d ≠ 0 := by
  intro hd
  apply M.det_ne_zero
  rw [hc, hd]
  ring

lemma denom_ne_zero_of_c_eq_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ) (hc : M.c = 0) :
    M.c * z + M.d ≠ 0 := by
  simpa [hc] using d_ne_zero_of_c_eq_zero M hc

lemma eval_some_eq_affine_of_c_eq_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ) (hc : M.c = 0) :
    M.eval (some z) = some ((M.a * z + M.b) / M.d) := by
  have hden := denom_ne_zero_of_c_eq_zero M z hc
  simpa [hc] using eval_some_eq_fractional_of_den_ne_zero M z hden

lemma eval_some_eq_slope_intercept_of_c_eq_zero
    (M : InfoGeometry.MobiusTransform) (z : ℂ) (hc : M.c = 0) :
    M.eval (some z) = some ((M.a / M.d) * z + M.b / M.d) := by
  rw [eval_some_eq_affine_of_c_eq_zero M z hc]
  congr 1
  have hd := d_ne_zero_of_c_eq_zero M hc
  field_simp [hd]

lemma cross_ratio_affine_case_finite
    (M : InfoGeometry.MobiusTransform) (z1 z2 z3 z4 : ℂ) (hc : M.c = 0) :
    InfoGeometry.cross_ratio
        ((M.a * z1 + M.b) / M.d)
        ((M.a * z2 + M.b) / M.d)
        ((M.a * z3 + M.b) / M.d)
        ((M.a * z4 + M.b) / M.d) =
      InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  have h1 := denom_ne_zero_of_c_eq_zero M z1 hc
  have h2 := denom_ne_zero_of_c_eq_zero M z2 hc
  have h3 := denom_ne_zero_of_c_eq_zero M z3 hc
  have h4 := denom_ne_zero_of_c_eq_zero M z4 hc
  simpa [hc] using cross_ratio_fractionalLinear_finite M z1 z2 z3 z4 h1 h2 h3 h4

lemma cross_ratio_eval_some_affine_case_preserving
    (M : InfoGeometry.MobiusTransform) (z1 z2 z3 z4 w1 w2 w3 w4 : ℂ)
    (hc : M.c = 0)
    (hw1 : M.eval (some z1) = some w1) (hw2 : M.eval (some z2) = some w2)
    (hw3 : M.eval (some z3) = some w3) (hw4 : M.eval (some z4) = some w4) :
    InfoGeometry.cross_ratio w1 w2 w3 w4 = InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  exact cross_ratio_eval_some_finite_preserving M z1 z2 z3 z4 w1 w2 w3 w4
    (denom_ne_zero_of_c_eq_zero M z1 hc)
    (denom_ne_zero_of_c_eq_zero M z2 hc)
    (denom_ne_zero_of_c_eq_zero M z3 hc)
    (denom_ne_zero_of_c_eq_zero M z4 hc)
    hw1 hw2 hw3 hw4

end Experimental.Sandbox.Mobius
