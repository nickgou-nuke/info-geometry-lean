import Experimental.Sandbox.Mobius.CanonicalCrossRatio

namespace Experimental.Sandbox.Mobius

lemma cross_ratio_self_first_third (z1 z2 z4 : ℂ) :
    InfoGeometry.cross_ratio z1 z2 z1 z4 = 0 := by
  unfold InfoGeometry.cross_ratio
  simp

lemma cross_ratio_self_second_fourth (z1 z2 z3 : ℂ) :
    InfoGeometry.cross_ratio z1 z2 z3 z2 = 0 := by
  unfold InfoGeometry.cross_ratio
  simp

lemma cross_ratio_one_of_first_second_equal (z1 z3 z4 : ℂ)
    (h13 : z1 - z3 ≠ 0) (h14 : z1 - z4 ≠ 0) :
    InfoGeometry.cross_ratio z1 z1 z3 z4 = 1 := by
  unfold InfoGeometry.cross_ratio
  field_simp [h13, h14]

lemma cross_ratio_one_of_third_fourth_equal (z1 z2 z3 : ℂ)
    (h23 : z2 - z3 ≠ 0) (h13 : z1 - z3 ≠ 0) :
    InfoGeometry.cross_ratio z1 z2 z3 z3 = 1 := by
  unfold InfoGeometry.cross_ratio
  field_simp [h23, h13]

lemma cross_ratio_zero_of_num_left_zero (z1 z2 z3 z4 : ℂ)
    (h : z1 - z3 = 0) :
    InfoGeometry.cross_ratio z1 z2 z3 z4 = 0 := by
  unfold InfoGeometry.cross_ratio
  rw [h]
  simp

lemma cross_ratio_zero_of_num_right_zero (z1 z2 z3 z4 : ℂ)
    (h : z2 - z4 = 0) :
    InfoGeometry.cross_ratio z1 z2 z3 z4 = 0 := by
  unfold InfoGeometry.cross_ratio
  rw [h]
  simp

end Experimental.Sandbox.Mobius
