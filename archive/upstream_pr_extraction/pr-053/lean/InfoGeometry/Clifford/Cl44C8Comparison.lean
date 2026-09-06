import InfoGeometry.Canonical.SplitBottPeriodicityBridge

open scoped TensorProduct

namespace InfoGeometry.Clifford.Cl44C8Comparison

/-- Honest owner equivalence for the split `Cl(4,4)` complexification corridor. -/
noncomputable abbrev cl44_complexification_is_C8 :
    InfoGeometry.Clifford.SplitCl44Complexification.Cl44Complex ≃ₐ[ℂ]
      ℂ ⊗[ℝ] InfoGeometry.Clifford.BottPeriodicity.Cl44 :=
  InfoGeometry.Canonical.SplitBottPeriodicityBridge.cl44_complexification_anchor

theorem cl44_complexification_is_C8_eq_owner :
    cl44_complexification_is_C8 =
      InfoGeometry.Canonical.SplitBottPeriodicityBridge.cl44_complexification_anchor :=
  rfl

end InfoGeometry.Clifford.Cl44C8Comparison
