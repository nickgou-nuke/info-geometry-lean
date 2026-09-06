import Experimental.Sandbox.Mobius.EvalCases

namespace Experimental.Sandbox.Mobius

lemma fractionalLinear_sub
    (M : InfoGeometry.MobiusTransform) (z w : ℂ)
    (hz : M.c * z + M.d ≠ 0) (hw : M.c * w + M.d ≠ 0) :
    (M.a * z + M.b) / (M.c * z + M.d) - (M.a * w + M.b) / (M.c * w + M.d) =
      (M.a * M.d - M.b * M.c) * (z - w) /
        ((M.c * z + M.d) * (M.c * w + M.d)) := by
  have hzc : z * M.c + M.d ≠ 0 := by simpa [mul_comm] using hz
  have hwc : w * M.c + M.d ≠ 0 := by simpa [mul_comm] using hw
  field_simp [hz, hw, hzc, hwc]
  ring

lemma cross_ratio_fractionalLinear_finite
    (M : InfoGeometry.MobiusTransform) (z1 z2 z3 z4 : ℂ)
    (h1 : M.c * z1 + M.d ≠ 0) (h2 : M.c * z2 + M.d ≠ 0)
    (h3 : M.c * z3 + M.d ≠ 0) (h4 : M.c * z4 + M.d ≠ 0) :
    InfoGeometry.cross_ratio
        ((M.a * z1 + M.b) / (M.c * z1 + M.d))
        ((M.a * z2 + M.b) / (M.c * z2 + M.d))
        ((M.a * z3 + M.b) / (M.c * z3 + M.d))
        ((M.a * z4 + M.b) / (M.c * z4 + M.d)) =
      InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  unfold InfoGeometry.cross_ratio
  rw [fractionalLinear_sub M z1 z3 h1 h3]
  rw [fractionalLinear_sub M z2 z4 h2 h4]
  rw [fractionalLinear_sub M z2 z3 h2 h3]
  rw [fractionalLinear_sub M z1 z4 h1 h4]
  field_simp [M.det_ne_zero, h1, h2, h3, h4]

lemma cross_ratio_eval_some_finite_preserving
    (M : InfoGeometry.MobiusTransform) (z1 z2 z3 z4 w1 w2 w3 w4 : ℂ)
    (h1 : M.c * z1 + M.d ≠ 0) (h2 : M.c * z2 + M.d ≠ 0)
    (h3 : M.c * z3 + M.d ≠ 0) (h4 : M.c * z4 + M.d ≠ 0)
    (hw1 : M.eval (some z1) = some w1) (hw2 : M.eval (some z2) = some w2)
    (hw3 : M.eval (some z3) = some w3) (hw4 : M.eval (some z4) = some w4) :
    InfoGeometry.cross_ratio w1 w2 w3 w4 = InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  have e1 := eval_some_eq_fractional_of_den_ne_zero M z1 h1
  have e2 := eval_some_eq_fractional_of_den_ne_zero M z2 h2
  have e3 := eval_some_eq_fractional_of_den_ne_zero M z3 h3
  have e4 := eval_some_eq_fractional_of_den_ne_zero M z4 h4
  injection hw1.symm.trans e1 with ew1
  injection hw2.symm.trans e2 with ew2
  injection hw3.symm.trans e3 with ew3
  injection hw4.symm.trans e4 with ew4
  subst w1
  subst w2
  subst w3
  subst w4
  exact cross_ratio_fractionalLinear_finite M z1 z2 z3 z4 h1 h2 h3 h4

end Experimental.Sandbox.Mobius
