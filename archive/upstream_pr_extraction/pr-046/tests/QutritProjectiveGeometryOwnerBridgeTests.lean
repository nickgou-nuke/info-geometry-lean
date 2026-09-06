import InfoGeometry.Quantum.QutritProjectiveGeometryOwnerBridge

open scoped LinearAlgebra.Projectivization
open InfoGeometry.Quantum.QutritProjectiveGeometryOwnerBridge

#check CP1Carrier
#check CP1OnRiemann
#check BiSplitCP1Carrier
#check BiSplitTripleCP1Carrier
#check TwistorProjectiveCarrier
#check CP1Veronese2
#check CP1Veronese2_ne_zero
#check CP1_to_ColorCP2
#check CP1Veronese3
#check CP1Veronese3_ne_zero
#check CP1_to_ColorSingletCP3
#check CP1_BranchCover

def cp1_nonzero_point : CP1Carrier := {
  z1 := 1,
  z2 := 0,
  not_both_zero := Or.inl one_ne_zero
}

example : CP1Veronese2 cp1_nonzero_point ≠ 0 := by
  exact CP1Veronese2_ne_zero cp1_nonzero_point

example : CP1Veronese3 cp1_nonzero_point ≠ 0 := by
  exact CP1Veronese3_ne_zero cp1_nonzero_point

example :
    (CP1_BranchCover 2 (by decide) cp1_nonzero_point).z1 = (1 : ℂ) ^ 2 := by
  rfl

example :
    (CP1_BranchCover 2 (by decide) cp1_nonzero_point).z2 = (0 : ℂ) ^ 2 := by
  rfl
