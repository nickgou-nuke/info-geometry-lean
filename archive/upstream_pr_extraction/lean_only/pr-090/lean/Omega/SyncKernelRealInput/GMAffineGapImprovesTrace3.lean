import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Baseline residual channel exponent corresponding to the un-improved `M^4` bound. -/
def baselineChannelExponent : ℝ :=
  4

/-- Improved residual channel exponent coming from the affine spectral gap. -/
def residualChannelExponent (sigma : ℝ) : ℝ :=
  4 - sigma

/-- Strict power saving means the residual exponent is below the baseline `M^4` exponent. -/
def strictPowerSaving (sigma : ℝ) : Prop :=
  residualChannelExponent sigma < baselineChannelExponent

/-- The balance threshold shift is a concrete exponent-level displacement. -/
noncomputable def balanceThresholdShift (sigma : ℝ) : ℝ :=
  sigma / 2

/-- The threshold displacement is computable from the spectral gap and is strictly positive. -/
def balanceThresholdComputable (sigma : ℝ) : Prop :=
  ∃ shift : ℝ, shift = balanceThresholdShift sigma ∧ 0 < shift

/-- Paper label: `prop:gm-affine-gap-improves-trace3`. -/
theorem paper_gm_affine_gap_improves_trace3
    (sigma : ℝ) (sigma_pos : 0 < sigma) :
    strictPowerSaving sigma ∧ balanceThresholdComputable sigma := by
  constructor
  · dsimp [strictPowerSaving, residualChannelExponent, baselineChannelExponent]
    linarith
  · refine ⟨balanceThresholdShift sigma, rfl, ?_⟩
    dsimp [balanceThresholdShift]
    linarith

end Omega.SyncKernelRealInput
