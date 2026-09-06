import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic
import InfoGeometry.Canonical.TwelveFoldExplicitOperators

/-!
# Native arithmetic of the twelvefold operator

This file records the divisor arithmetic forced by the already constructed
operator `masterTwelve`.  The statements are made directly in the concrete
matrix monoid; no scalar diagonalisation or auxiliary witness structure is
introduced.
-/

namespace InfoGeometry.Canonical.TwelveFoldArithmeticNative

open InfoGeometry.Canonical.TwelveFoldExplicitOperators
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl
open InfoGeometry.Canonical.HexagonalSixRootTiling
open InfoGeometry.Canonical.SixStateSpectralBridge

noncomputable section

theorem masterTwelve_orderOf_pow (k : ℕ) (hk : k ≠ 0) :
    orderOf (masterTwelve ^ k) = 12 / Nat.gcd 12 k := by
  calc
    orderOf (masterTwelve ^ k) = orderOf masterTwelve / (orderOf masterTwelve).gcd k :=
      orderOf_pow' masterTwelve hk
    _ = 12 / Nat.gcd 12 k := by rw [masterTwelve_order_exact]

theorem masterTwelve_pow_eq_one_iff (n : ℕ) :
    masterTwelve ^ n =
        (1 : TwelveFoldExplicitOperators.Mat23C) ↔ 12 ∣ n := by
  rw [← orderOf_dvd_iff_pow_eq_one, masterTwelve_order_exact]

theorem primitive_twelfth_exponent_iff {k : ℕ} (hk : k < 12) :
    Nat.Coprime k 12 ↔ k = 1 ∨ k = 5 ∨ k = 7 ∨ k = 11 := by
  interval_cases k <;> norm_num

theorem primitive_twelfth_exponent_square_mod_twelve {k : ℕ}
    (hk : k < 12) (hc : Nat.Coprime k 12) : k * k % 12 = 1 := by
  rcases (primitive_twelfth_exponent_iff hk).mp hc with rfl | rfl | rfl | rfl <;>
    norm_num

theorem sixTriality_order : orderOf sixTriality = 6 := by
  rw [← masterTwelve_sq, masterTwelve_orderOf_pow 2 (by norm_num)]
  norm_num

theorem omegaHat_order : orderOf omegaHat = 4 := by
  rw [← masterTwelve_cube, masterTwelve_orderOf_pow 3 (by norm_num)]
  norm_num

theorem sixParity_order : orderOf sixParity = 2 := by
  rw [← masterTwelve_six, masterTwelve_orderOf_pow 6 (by norm_num)]
  norm_num

theorem sixShift_order : orderOf sixShift = 3 := by
  rw [← masterTwelve_eight, masterTwelve_orderOf_pow 8 (by norm_num)]
  norm_num

theorem sixTriality_cube_eq_sixParity : sixTriality ^ 3 = sixParity := by
  calc
    sixTriality ^ 3 = (masterTwelve ^ 2) ^ 3 := by rw [masterTwelve_sq]
    _ = masterTwelve ^ 6 := by rw [← pow_mul]
    _ = sixParity := masterTwelve_six

theorem omegaHat_sq_eq_sixParity : omegaHat ^ 2 = sixParity := omegaHat_sq

theorem common_order_two_projection :
    sixTriality ^ 3 = omegaHat ^ 2 := by
  rw [sixTriality_cube_eq_sixParity, omegaHat_sq]

theorem sixParity_is_unique_order_two_power :
    masterTwelve ^ 6 = sixParity := masterTwelve_six

theorem sixShift_cube_eq_one :
    sixShift ^ 3 = (1 : TwelveFoldExplicitOperators.Mat23C) := by
  rw [← masterTwelve_eight]
  calc
    (masterTwelve ^ 8) ^ 3 = masterTwelve ^ 24 := by rw [← pow_mul]
    _ = (masterTwelve ^ 12) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [masterTwelve_twelve]; simp

theorem zmod12_units_card : Fintype.card (ZMod 12)ˣ = 4 := by
  decide

theorem zmod12_units_sq_one (u : (ZMod 12)ˣ) : u ^ 2 = 1 := by
  fin_cases u <;> decide

theorem zmod12_units_order_dvd_two (u : (ZMod 12)ˣ) : orderOf u ∣ 2 := by
  rw [orderOf_dvd_iff_pow_eq_one]
  exact zmod12_units_sq_one u

theorem zmod12_units_exponent_two : Monoid.exponent (ZMod 12)ˣ = 2 := by
  have hpow : ∀ u : (ZMod 12)ˣ, u ^ 2 = 1 := zmod12_units_sq_one
  have hdiv : Monoid.exponent (ZMod 12)ˣ ∣ 2 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
  have hle : Monoid.exponent (ZMod 12)ˣ ≤ 2 :=
    Nat.le_of_dvd (by decide) hdiv
  have hne1 : Monoid.exponent (ZMod 12)ˣ ≠ 1 := by
    intro h1
    let u5 : (ZMod 12)ˣ := Units.mkOfMulEqOne (5 : ZMod 12) 5 (by decide)
    have hu5 : u5 ≠ 1 := by
      intro hu
      have h : (5 : ZMod 12) = 1 := by
        simpa [u5] using congrArg Units.val hu
      exact (by decide : (5 : ZMod 12) ≠ 1) h
    exact hu5 (by simpa [h1, u5] using Monoid.pow_exponent_eq_one u5)
  have hpos : 0 < Monoid.exponent (ZMod 12)ˣ := by
    have hexists : Monoid.ExponentExists (ZMod 12)ˣ :=
      ⟨2, by decide, hpow⟩
    exact Monoid.exponent_pos.mpr hexists
  omega

theorem zmod12_units_isKleinFour : IsKleinFour (ZMod 12)ˣ := by
  refine IsKleinFour.mk ?_ zmod12_units_exponent_two
  simpa [Nat.card_eq_fintype_card] using zmod12_units_card

end
end InfoGeometry.Canonical.TwelveFoldArithmeticNative
