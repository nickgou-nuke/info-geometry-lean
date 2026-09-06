import proofs.TwelveFoldCharacteristicPolynomial

/-!
# Exact order hierarchy of the twelvefold master operator

The master operator is a faithful generator: a natural power is the identity
exactly when its exponent is divisible by twelve.  Its distinguished powers
recover the order-six triality, order-four sheet phase, order-two parity, and
order-three colour shift.
-/

noncomputable section
namespace TwelveFoldOrderHierarchy

open TwoSheetThreeColorWeyl TwelveFoldSheetColorOmega
open TwelveFoldSpectralBridge

theorem masterTwelve_pow_eq_one_iff (n : ℕ) :
    masterTwelve ^ n = (1 : M6C) ↔ 12 ∣ n := by
  rw [← orderOf_dvd_iff_pow_eq_one, masterTwelve_orderOf]

theorem masterTwelve_sq_order : orderOf (masterTwelve ^ 2) = 6 := by
  rw [orderOf_pow' masterTwelve (by norm_num), masterTwelve_orderOf]
  norm_num

theorem masterTwelve_cube_order : orderOf (masterTwelve ^ 3) = 4 := by
  rw [orderOf_pow' masterTwelve (by norm_num), masterTwelve_orderOf]
  norm_num

theorem masterTwelve_six_order : orderOf (masterTwelve ^ 6) = 2 := by
  rw [orderOf_pow' masterTwelve (by norm_num), masterTwelve_orderOf]
  norm_num

theorem masterTwelve_eight_order : orderOf (masterTwelve ^ 8) = 3 := by
  rw [orderOf_pow' masterTwelve (by norm_num), masterTwelve_orderOf]
  norm_num

theorem sixfoldTriality_order : orderOf sixfoldTriality = 6 := by
  rw [← masterTwelve_sq]
  exact masterTwelve_sq_order

theorem omegaSheetSix_order : orderOf omegaSheetSix = 4 := by
  rw [← masterTwelve_cube]
  exact masterTwelve_cube_order

theorem sheetParitySix_order :
    orderOf (tensor sheetGamma (1 : M3C)) = 2 := by
  rw [← masterTwelve_six]
  exact masterTwelve_six_order

theorem colorShiftSix_order :
    orderOf colorShiftSix = 3 := by
  rw [← masterTwelve_eight]
  exact masterTwelve_eight_order

theorem colorShiftTensor_order :
    orderOf (tensor (1 : M2C) colorShift) = 3 := by
  simpa [colorShiftSix] using colorShiftSix_order

theorem twelvefold_order_hierarchy_packet :
    orderOf masterTwelve = 12 ∧
    orderOf sixfoldTriality = 6 ∧
    orderOf omegaSheetSix = 4 ∧
    orderOf (tensor sheetGamma (1 : M3C)) = 2 ∧
    orderOf (tensor (1 : M2C) colorShift) = 3 :=
  ⟨masterTwelve_orderOf, sixfoldTriality_order, omegaSheetSix_order,
    sheetParitySix_order, colorShiftTensor_order⟩

end TwelveFoldOrderHierarchy
end noncomputable section
