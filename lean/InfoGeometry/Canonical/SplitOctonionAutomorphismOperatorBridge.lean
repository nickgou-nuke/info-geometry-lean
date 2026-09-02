import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Algebra.AlternativeDerivations

/-! Automorphisms transport regular multiplication operators. -/
noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge

open InfoGeometry.Canonical

abbrev Carrier := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCarrier := Module.End ℝ Carrier

abbrev leftRegular := InfoGeometry.Algebra.L_map (R := ℝ)

def conjugateLeftRegular (φ : RealSplitOctonionAut) (x : Carrier) : EndCarrier :=
  φ.1.toLinearMap * leftRegular x * φ.1.symm.toLinearMap

theorem conjugateLeftRegular_apply (φ : RealSplitOctonionAut) (x y : Carrier) :
    conjugateLeftRegular φ x y = φ.1 (x * φ.1.symm y) := by
  simp [conjugateLeftRegular, leftRegular, InfoGeometry.Algebra.L_map]

theorem conjugateLeftRegular_eq_leftRegular (φ : RealSplitOctonionAut) (x : Carrier) :
    conjugateLeftRegular φ x = leftRegular ((φ.1 : Carrier) x) := by
  ext y
  rw [conjugateLeftRegular_apply]
  rw [← φ.preserves_mul]
  simp

end InfoGeometry.Canonical.SplitOctonionAutomorphismOperatorBridge
end noncomputable section
