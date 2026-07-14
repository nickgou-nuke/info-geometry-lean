import InfoGeometry.Topology.MobiusGeometry

/-!
# MobiusNormalizationHelpers

Small sandbox packet for the concrete normalization moves used in the 3-transitivity story.
-/

namespace InfoGeometry.Restore.MobiusNormalizationHelpers

open Complex

/-- Translation acts by adding the translation parameter on finite points. -/
theorem translation_transform_eval_some (b z : ℂ) :
    InfoGeometry.MobiusTransform.eval (InfoGeometry.translation_transform b) (some z) =
      some (z + b) := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.translation_transform]

/-- Translation fixes the point at infinity. -/
theorem translation_transform_eval_none (b : ℂ) :
    InfoGeometry.MobiusTransform.eval (InfoGeometry.translation_transform b) none = none := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.translation_transform]

/-- Dilation acts by scalar multiplication on finite points. -/
theorem dilation_transform_eval_some (a z : ℂ) (ha : a ≠ 0) :
    InfoGeometry.MobiusTransform.eval (InfoGeometry.dilation_transform a ha) (some z) =
      some (a * z) := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.dilation_transform, ha]

/-- Dilation fixes the point at infinity. -/
theorem dilation_transform_eval_none (a : ℂ) (ha : a ≠ 0) :
    InfoGeometry.MobiusTransform.eval (InfoGeometry.dilation_transform a ha) none = none := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.dilation_transform, ha]

/-- Inversion sends zero to infinity. -/
theorem inversion_transform_eval_zero :
    InfoGeometry.MobiusTransform.eval InfoGeometry.inversion_transform (some 0) = none := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.inversion_transform]

/-- Inversion sends infinity to zero. -/
theorem inversion_transform_eval_none :
    InfoGeometry.MobiusTransform.eval InfoGeometry.inversion_transform none = some 0 := by
  simp [InfoGeometry.MobiusTransform.eval, InfoGeometry.inversion_transform]

end InfoGeometry.Restore.MobiusNormalizationHelpers
