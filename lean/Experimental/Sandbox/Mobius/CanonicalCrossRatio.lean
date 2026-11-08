import Experimental.Sandbox.Mobius.CanonicalTransforms

namespace Experimental.Sandbox.Mobius

lemma cross_ratio_translation_finite (z1 z2 z3 z4 b : ℂ) :
    InfoGeometry.cross_ratio (z1 + b) (z2 + b) (z3 + b) (z4 + b) =
      InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  unfold InfoGeometry.cross_ratio
  ring

lemma cross_ratio_dilation_finite (z1 z2 z3 z4 a : ℂ) (ha : a ≠ 0) :
    InfoGeometry.cross_ratio (a * z1) (a * z2) (a * z3) (a * z4) =
      InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  unfold InfoGeometry.cross_ratio
  field_simp [ha]

lemma cross_ratio_inversion_finite (z1 z2 z3 z4 : ℂ)
    (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) (h3 : z3 ≠ 0) (h4 : z4 ≠ 0) :
    InfoGeometry.cross_ratio z1⁻¹ z2⁻¹ z3⁻¹ z4⁻¹ =
      InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  unfold InfoGeometry.cross_ratio
  field_simp [h1, h2, h3, h4]
  ring

lemma cross_ratio_translation_eval_some_preserving
    (b z1 z2 z3 z4 w1 w2 w3 w4 : ℂ)
    (hw1 : (InfoGeometry.translation_transform b).eval (some z1) = some w1)
    (hw2 : (InfoGeometry.translation_transform b).eval (some z2) = some w2)
    (hw3 : (InfoGeometry.translation_transform b).eval (some z3) = some w3)
    (hw4 : (InfoGeometry.translation_transform b).eval (some z4) = some w4) :
    InfoGeometry.cross_ratio w1 w2 w3 w4 = InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  rw [translation_eval_some] at hw1
  rw [translation_eval_some] at hw2
  rw [translation_eval_some] at hw3
  rw [translation_eval_some] at hw4
  injection hw1 with e1
  injection hw2 with e2
  injection hw3 with e3
  injection hw4 with e4
  subst w1
  subst w2
  subst w3
  subst w4
  exact cross_ratio_translation_finite z1 z2 z3 z4 b

lemma cross_ratio_dilation_eval_some_preserving
    (a z1 z2 z3 z4 w1 w2 w3 w4 : ℂ) (ha : a ≠ 0)
    (hw1 : (InfoGeometry.dilation_transform a ha).eval (some z1) = some w1)
    (hw2 : (InfoGeometry.dilation_transform a ha).eval (some z2) = some w2)
    (hw3 : (InfoGeometry.dilation_transform a ha).eval (some z3) = some w3)
    (hw4 : (InfoGeometry.dilation_transform a ha).eval (some z4) = some w4) :
    InfoGeometry.cross_ratio w1 w2 w3 w4 = InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  rw [dilation_eval_some] at hw1
  rw [dilation_eval_some] at hw2
  rw [dilation_eval_some] at hw3
  rw [dilation_eval_some] at hw4
  injection hw1 with e1
  injection hw2 with e2
  injection hw3 with e3
  injection hw4 with e4
  subst w1
  subst w2
  subst w3
  subst w4
  exact cross_ratio_dilation_finite z1 z2 z3 z4 a ha

lemma cross_ratio_inversion_eval_some_preserving
    (z1 z2 z3 z4 w1 w2 w3 w4 : ℂ)
    (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) (h3 : z3 ≠ 0) (h4 : z4 ≠ 0)
    (hw1 : InfoGeometry.inversion_transform.eval (some z1) = some w1)
    (hw2 : InfoGeometry.inversion_transform.eval (some z2) = some w2)
    (hw3 : InfoGeometry.inversion_transform.eval (some z3) = some w3)
    (hw4 : InfoGeometry.inversion_transform.eval (some z4) = some w4) :
    InfoGeometry.cross_ratio w1 w2 w3 w4 = InfoGeometry.cross_ratio z1 z2 z3 z4 := by
  rw [inversion_eval_some_of_ne_zero z1 h1] at hw1
  rw [inversion_eval_some_of_ne_zero z2 h2] at hw2
  rw [inversion_eval_some_of_ne_zero z3 h3] at hw3
  rw [inversion_eval_some_of_ne_zero z4 h4] at hw4
  injection hw1 with e1
  injection hw2 with e2
  injection hw3 with e3
  injection hw4 with e4
  subst w1
  subst w2
  subst w3
  subst w4
  exact cross_ratio_inversion_finite z1 z2 z3 z4 h1 h2 h3 h4

end Experimental.Sandbox.Mobius
