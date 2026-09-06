import Experimental.Sandbox.Mobius.CompositionFinite
import Experimental.Sandbox.Mobius.InverseFinite

namespace Experimental.Sandbox.Mobius

lemma det_inv_eq_det (M : InfoGeometry.MobiusTransform) :
    (InfoGeometry.inv M).a * (InfoGeometry.inv M).d -
        (InfoGeometry.inv M).b * (InfoGeometry.inv M).c =
      M.a * M.d - M.b * M.c := by
  simp [InfoGeometry.inv]
  ring

lemma det_comp_eq_mul_det (M1 M2 : InfoGeometry.MobiusTransform) :
    (InfoGeometry.comp M1 M2).a * (InfoGeometry.comp M1 M2).d -
        (InfoGeometry.comp M1 M2).b * (InfoGeometry.comp M1 M2).c =
      (M1.a * M1.d - M1.b * M1.c) * (M2.a * M2.d - M2.b * M2.c) := by
  simp [InfoGeometry.comp]
  ring

lemma comp_det_ne_zero (M1 M2 : InfoGeometry.MobiusTransform) :
    (InfoGeometry.comp M1 M2).a * (InfoGeometry.comp M1 M2).d -
        (InfoGeometry.comp M1 M2).b * (InfoGeometry.comp M1 M2).c ≠ 0 := by
  rw [det_comp_eq_mul_det]
  exact mul_ne_zero M1.det_ne_zero M2.det_ne_zero

lemma inv_det_ne_zero (M : InfoGeometry.MobiusTransform) :
    (InfoGeometry.inv M).a * (InfoGeometry.inv M).d -
        (InfoGeometry.inv M).b * (InfoGeometry.inv M).c ≠ 0 := by
  rw [det_inv_eq_det]
  exact M.det_ne_zero

lemma det_translation_transform (b : ℂ) :
    (InfoGeometry.translation_transform b).a * (InfoGeometry.translation_transform b).d -
        (InfoGeometry.translation_transform b).b * (InfoGeometry.translation_transform b).c = 1 := by
  simp [InfoGeometry.translation_transform]

lemma det_dilation_transform (a : ℂ) (ha : a ≠ 0) :
    (InfoGeometry.dilation_transform a ha).a * (InfoGeometry.dilation_transform a ha).d -
        (InfoGeometry.dilation_transform a ha).b * (InfoGeometry.dilation_transform a ha).c = a := by
  simp [InfoGeometry.dilation_transform]

lemma det_inversion_transform :
    InfoGeometry.inversion_transform.a * InfoGeometry.inversion_transform.d -
        InfoGeometry.inversion_transform.b * InfoGeometry.inversion_transform.c = -1 := by
  simp [InfoGeometry.inversion_transform]

end Experimental.Sandbox.Mobius
