import Mathlib.Tactic

noncomputable section

namespace BPSPositiveEnergyBound

/-- Positivity of the real operator eigenvalue `2(M-Z)` gives the one-sided BPS inequality. -/
theorem bps_bound_of_positive_minus (M Z : ℝ) (h : 0 ≤ 2 * (M - Z)) :
    Z ≤ M := by
  nlinarith

/-- Positivity of the conjugate real eigenvalue `2(M+Z)` gives the opposite side. -/
theorem bps_bound_of_positive_plus (M Z : ℝ) (h : 0 ≤ 2 * (M + Z)) :
    -M ≤ Z := by
  nlinarith

/-- The two positive supercharge combinations imply the real BPS bound `|Z| ≤ M`. -/
theorem abs_central_charge_le_mass (M Z : ℝ)
    (hminus : 0 ≤ 2 * (M - Z))
    (hplus : 0 ≤ 2 * (M + Z)) :
    |Z| ≤ M := by
  rw [abs_le]
  exact ⟨bps_bound_of_positive_plus M Z hplus, bps_bound_of_positive_minus M Z hminus⟩

/-- Saturation of the minus channel means `M=Z`. -/
theorem bps_saturation_minus (M Z : ℝ) (h : 2 * (M - Z) = 0) :
    M = Z := by
  nlinarith

/-- Saturation of the plus channel means `M=-Z`. -/
theorem bps_saturation_plus (M Z : ℝ) (h : 2 * (M + Z) = 0) :
    M = -Z := by
  nlinarith

/-- If the BPS bound is saturated by a nonnegative central charge, then `M=|Z|`. -/
theorem bps_saturation_abs_of_nonneg (M Z : ℝ) (hZ : 0 ≤ Z) (h : M = Z) :
    M = |Z| := by
  rw [h, abs_of_nonneg hZ]

#check bps_bound_of_positive_minus
#check bps_bound_of_positive_plus
#check abs_central_charge_le_mass
#check bps_saturation_minus
#check bps_saturation_plus
#check bps_saturation_abs_of_nonneg

end BPSPositiveEnergyBound
