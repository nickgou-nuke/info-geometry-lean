/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2NativeFlagResidualPivots

/-! Close the native residual using the cleared pivots and preserved products. -/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagResidualClosure

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2TwoPCRecovery G2NativeFlagStabilizerTransport G2NativeFlagResidualPivots
open G2NativeFlagStabilizerClosureReadback G2NativeFlagStabilizerLastBitClosure
open G2ImaginaryOctImBridge

theorem fullPeel_basis8_two_reduced_shape {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ b : F2Bit, (fullPeel g).1 (basis8 2) =
      ⟨b, b, true, false, false, b, false, false⟩ := by
  obtain ⟨a, x1, y0, y1, hs, hr⟩ := fullPeel_basis8_two_residual_coordinate_certificate hg
  have hx := fullPeel_basis8_two_x1_false_of_stabilizer hg
  have hy := fullPeel_basis8_two_y1_false hg
  rw [hs] at hx hy
  change x1 = false at hx
  change y1 = false at hy
  subst x1
  subst y1
  have hya : y0 = a := by simpa [add2, mul2] using hr
  subst y0
  exact ⟨a, hs⟩

theorem fullPeel_basis8_seven_fixed {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (fullPeel g).1 (basis8 7) = basis8 7 := by
  let f := fullPeel g
  have h4 : f.1 (basis8 4) = basis8 4 := fullPeel_basis8_four_readback hg
  have h5 : f.1 (basis8 5) = basis8 5 := fullPeel_basis8_five_readback hg
  have hp : mul (basis8 4) (f.1 (basis8 7)) = mul (f.1 (basis8 2)) (basis8 5) := by
    rw [← h4, ← h5, ← f.2.2.2, ← f.2.2.2]
    rfl
  have hz : mul (f.1 (basis8 2)) (f.1 (basis8 7)) = zero := by
    rw [← f.2.2.2]
    exact automorphism_map_zero f
  have ht : (mul (f.1 (basis8 7)) (basis8 5)).x2 = false := by
    rw [← h5, ← f.2.2.2]
    exact fullPeel_basis8_three_x2_false hg
  obtain ⟨b, h2⟩ := fullPeel_basis8_two_reduced_shape hg
  obtain ⟨a, c, d, h7⟩ := fullPeel_basis8_seven_residual_shape_of_stabilizer hg
  change f.1 (basis8 2) = _ at h2
  change f.1 (basis8 7) = _ at h7
  rw [h2, h7] at hp hz
  rw [h7] at ht
  change f.1 (basis8 7) = basis8 7
  rw [h7]
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [mul, dot3, cross0, cross1, cross2, basis8,
      up0, up1, up2, down0, down1, down2, ePlus, eMinus, zero, add2, mul2]

/-- Native flag stabilizers have no residual after PC recovery. -/
theorem fullPeel_eq_one_of_stabilizer {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) : fullPeel g = 1 := by
  exact fullPeel_eq_one_of_seven_and_six_y0 hg
    (fullPeel_basis8_seven_fixed hg)
    (fullPeel_basis8_six_y0_false_of_stabilizer hg)

/-- The stabilizer is the native unipotent subgroup, without a census assumption. -/
theorem nativeFlagStabilizer_eq_unipotent :
    nativeFlagStabilizer = G2TwoPCSubgroupClosure.unipotentSubgroup := by
  exact nativeFlagStabilizer_eq_unipotent_of_final_readbacks
    (fun _ hg => fullPeel_basis8_seven_fixed hg)
    (fun _ hg => fullPeel_basis8_six_y0_false_of_stabilizer hg)

/-- The native flag orbit has 189 cosets of the unipotent subgroup. -/
theorem quotient_card_eq_189 :
    Nat.card (SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup) = 189 := by
  exact quotient_card_eq_189_of_final_readbacks
    (fun _ hg => fullPeel_basis8_seven_fixed hg)
    (fun _ hg => fullPeel_basis8_six_y0_false_of_stabilizer hg)

/-- Count the native automorphism group using its proved flag stabilizer. -/
theorem ambient_card_eq_12096 : Nat.card SplitOctF2Aut = 12096 := by
  exact ambient_card_eq_12096_of_final_readbacks
    (fun _ hg => fullPeel_basis8_seven_fixed hg)
    (fun _ hg => fullPeel_basis8_six_y0_false_of_stabilizer hg)

end InfoGeometry.Algebra.Zorn.G2NativeFlagResidualClosure
