import Experimental.Sandbox.Mobius.CanonicalTransforms

namespace Experimental.Sandbox.Mobius

lemma mobius_ext
    {M N : InfoGeometry.MobiusTransform}
    (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c) (hd : M.d = N.d) :
    M = N := by
  cases M
  cases N
  simp at ha hb hc hd
  subst_vars
  rfl

lemma comp_translation_translation
    (b₁ b₂ : ℂ) :
    InfoGeometry.comp (InfoGeometry.translation_transform b₁) (InfoGeometry.translation_transform b₂) =
      InfoGeometry.translation_transform (b₁ + b₂) := by
  apply mobius_ext
  · simp [InfoGeometry.comp, InfoGeometry.translation_transform]
  · simp [InfoGeometry.comp, InfoGeometry.translation_transform]
    ring
  · simp [InfoGeometry.comp, InfoGeometry.translation_transform]
  · simp [InfoGeometry.comp, InfoGeometry.translation_transform]

lemma comp_dilation_dilation
    (a₁ a₂ : ℂ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    InfoGeometry.comp (InfoGeometry.dilation_transform a₁ ha₁) (InfoGeometry.dilation_transform a₂ ha₂) =
      InfoGeometry.dilation_transform (a₁ * a₂) (mul_ne_zero ha₁ ha₂) := by
  apply mobius_ext
  · simp [InfoGeometry.comp, InfoGeometry.dilation_transform]
  · simp [InfoGeometry.comp, InfoGeometry.dilation_transform]
  · simp [InfoGeometry.comp, InfoGeometry.dilation_transform]
  · simp [InfoGeometry.comp, InfoGeometry.dilation_transform]

lemma comp_translation_zero_left (b : ℂ) :
    InfoGeometry.comp (InfoGeometry.translation_transform 0) (InfoGeometry.translation_transform b) =
      InfoGeometry.translation_transform b := by
  simpa using comp_translation_translation (0 : ℂ) b

lemma comp_translation_zero_right (b : ℂ) :
    InfoGeometry.comp (InfoGeometry.translation_transform b) (InfoGeometry.translation_transform 0) =
      InfoGeometry.translation_transform b := by
  simpa using comp_translation_translation b (0 : ℂ)

lemma comp_translation_neg_left (b : ℂ) :
    InfoGeometry.comp (InfoGeometry.translation_transform (-b)) (InfoGeometry.translation_transform b) =
      InfoGeometry.translation_transform 0 := by
  simpa using comp_translation_translation (-b) b

lemma comp_translation_neg_right (b : ℂ) :
    InfoGeometry.comp (InfoGeometry.translation_transform b) (InfoGeometry.translation_transform (-b)) =
      InfoGeometry.translation_transform 0 := by
  simpa using comp_translation_translation b (-b)

lemma comp_dilation_one_left (a : ℂ) (ha : a ≠ 0) :
    InfoGeometry.comp (InfoGeometry.dilation_transform 1 one_ne_zero) (InfoGeometry.dilation_transform a ha) =
      InfoGeometry.dilation_transform a ha := by
  simpa using comp_dilation_dilation (1 : ℂ) a one_ne_zero ha

lemma comp_dilation_one_right (a : ℂ) (ha : a ≠ 0) :
    InfoGeometry.comp (InfoGeometry.dilation_transform a ha) (InfoGeometry.dilation_transform 1 one_ne_zero) =
      InfoGeometry.dilation_transform a ha := by
  simpa using comp_dilation_dilation a (1 : ℂ) ha one_ne_zero

end Experimental.Sandbox.Mobius
