import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

/-! Automorphisms transport regular multiplication operators. -/
noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge

open InfoGeometry.Canonical
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

abbrev Carrier := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCarrier := Module.End ℝ Carrier

noncomputable def leftRegular (x : Carrier) : EndCarrier :=
  leftMultiplication x

def conjugateLeftRegular (φ : RealSplitOctonionAut) (x : Carrier) : EndCarrier :=
  φ.1.toLinearMap * leftRegular x * φ.1.symm.toLinearMap

theorem conjugateLeftRegular_apply (φ : RealSplitOctonionAut) (x y : Carrier) :
    conjugateLeftRegular φ x y = φ.1 (x * φ.1.symm y) := by
  simp [conjugateLeftRegular, leftRegular, leftMultiplication_apply]

theorem conjugateLeftRegular_eq_leftRegular (φ : RealSplitOctonionAut) (x : Carrier) :
    conjugateLeftRegular φ x = leftRegular (φ.1 x) := by
  apply LinearMap.ext
  intro y
  rw [conjugateLeftRegular_apply, φ.preserves_mul]
  simp [leftRegular, leftMultiplication_apply]

end InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge
end noncomputable section
