import InfoGeometry.Canonical.SplitBottPeriodicityBridge

open scoped TensorProduct

namespace InfoGeometry.Clifford.Cl44C8Comparison

/--
Honest owner theorem for the split `Cl(4,4)` complexification corridor.

The repo-owned statement is the algebraic base-change equivalence already
proved in `Canonical.SplitBottPeriodicityBridge`. The external paper naming of
the target as `C(8)` is not formalized here as a separate identification.
-/
theorem cl44_complexification_is_C8 :
    Nonempty
      (InfoGeometry.Clifford.SplitCl44Complexification.Cl44Complex ≃ₐ[ℂ]
        ℂ ⊗[ℝ] InfoGeometry.Clifford.BottPeriodicity.Cl44) :=
  InfoGeometry.Canonical.SplitBottPeriodicityBridge.cl44_complexification_anchor

end InfoGeometry.Clifford.Cl44C8Comparison
