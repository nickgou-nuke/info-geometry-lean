import InfoGeometry.Quantum.QutritProjectiveColorBridge
import InfoGeometry.Quantum.QutritProjectiveGeometryOwnerBridge

open scoped LinearAlgebra.Projectivization
open InfoGeometry.Quantum.QutritProjectiveColorBridge
open InfoGeometry.Quantum.QutritProjectiveGeometryOwnerBridge

#check ColorCP2
#check ColorSingletCP3
#check PenroseCP3
#check CP1Carrier
#check CP1OnRiemann
#check BiSplitCP1Carrier
#check BiSplitTripleCP1Carrier
#check CP1Veronese2
#check CP1Veronese2_ne_zero
#check CP1_to_ColorCP2
#check CP1Veronese3
#check CP1Veronese3_ne_zero
#check CP1_to_ColorSingletCP3
#check CP1_BranchCover
#check CP1Veronese2
#check CP1_to_ColorCP2

example : CP1Veronese3 ({ z1 := 1, z2 := 0, not_both_zero := Or.inl one_ne_zero } : CP1Carrier) ≠ 0 := by
  simpa using (CP1Veronese3_ne_zero ({ z1 := 1, z2 := 0, not_both_zero := Or.inl one_ne_zero } : CP1Carrier))

example : CP1_BranchCover 2 (by decide) ({ z1 := 1, z2 := 0, not_both_zero := Or.inl one_ne_zero })
    = { z1 := 1 ^ 2, z2 := 0 ^ 2, not_both_zero := Or.inl (by norm_num) } := by
  rfl

example : CP1_to_ColorCP2 ({ z1 := 1, z2 := 1, not_both_zero := Or.inl one_ne_zero })
    = CP1_to_ColorCP2 ({ z1 := 1, z2 := 1, not_both_zero := Or.inl one_ne_zero }) := by
  simp
