import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Tetron Parity Lifetime Bridge

A theorem-honest finite model for comparing superconducting tetron parity
lifetimes with the photonic parity-transfer analogy.

The model is deliberately modest: it formalizes only an Arrhenius-style lifetime
law

`τ(Δ,T) = τ₀ exp(Δ/T)`

and its monotonic consequences.  It does **not** claim that a room-temperature
photonic chip literally stores fermionic parity for 20 seconds; the photonic
system can simulate parity transfer/contrast, while long-lived memory requires a
separate storage mechanism.
-/

noncomputable section

open Real

namespace InfoGeometry.GrandUnification.TetronParityLifetimeBridge

/-- Arrhenius-style parity lifetime model with effective gap `gap` and temperature scale `theta`. -/
def parityLifetime (tau0 gap theta : ℝ) : ℝ :=
  tau0 * Real.exp (gap / theta)

/-- Lifetime ratio at two gaps with the same prefactor and temperature scale. -/
def lifetimeRatio (gap1 gap2 theta : ℝ) : ℝ :=
  Real.exp ((gap2 - gap1) / theta)

/-- Optical propagation time through a chip of length `L` at group velocity `vg`. -/
def opticalPropagationTime (L vg : ℝ) : ℝ :=
  L / vg

/-- If the effective gap is increased, the Arrhenius lifetime does not decrease. -/
theorem parityLifetime_mono_gap
    {tau0 theta gap1 gap2 : ℝ} (htau : 0 ≤ tau0) (htheta : 0 < theta) (hgap : gap1 ≤ gap2) :
    parityLifetime tau0 gap1 theta ≤ parityLifetime tau0 gap2 theta := by
  unfold parityLifetime
  apply mul_le_mul_of_nonneg_left _ htau
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right hgap (le_of_lt htheta)

/-- The ratio formula: `τ(gap2)/τ(gap1) = exp((gap2-gap1)/theta)` for nonzero prefactor. -/
theorem parityLifetime_ratio_formula
    {tau0 gap1 gap2 theta : ℝ} (htau : tau0 ≠ 0) :
    parityLifetime tau0 gap2 theta / parityLifetime tau0 gap1 theta =
      lifetimeRatio gap1 gap2 theta := by
  unfold parityLifetime lifetimeRatio
  field_simp [htau, Real.exp_ne_zero]
  have h : gap2 / theta = gap1 / theta + (gap2 - gap1) / theta := by ring
  rw [h, Real.exp_add]

/-- Calibrating the microscopic prefactor from one measured lifetime. -/
def calibratedTau0 (measuredLifetime measuredGap theta : ℝ) : ℝ :=
  measuredLifetime / Real.exp (measuredGap / theta)

/-- Calibration reproduces the measured lifetime exactly. -/
theorem calibratedTau0_reproduces (tau gap theta : ℝ) :
    parityLifetime (calibratedTau0 tau gap theta) gap theta = tau := by
  unfold parityLifetime calibratedTau0
  field_simp [Real.exp_ne_zero]

/-- Propagation time in a passive chip is positive when length and group velocity are positive. -/
theorem opticalPropagationTime_pos {L vg : ℝ} (hL : 0 < L) (hvg : 0 < vg) :
    0 < opticalPropagationTime L vg := by
  unfold opticalPropagationTime
  positivity

/-- Consolidated lifetime bridge package. -/
theorem tetron_parity_lifetime_bridge_synthesis :
    (∀ {tau0 theta gap1 gap2 : ℝ}, 0 ≤ tau0 → 0 < theta → gap1 ≤ gap2 →
      parityLifetime tau0 gap1 theta ≤ parityLifetime tau0 gap2 theta) ∧
    (∀ {tau0 gap1 gap2 theta : ℝ}, tau0 ≠ 0 →
      parityLifetime tau0 gap2 theta / parityLifetime tau0 gap1 theta = lifetimeRatio gap1 gap2 theta) ∧
    (∀ tau gap theta : ℝ, parityLifetime (calibratedTau0 tau gap theta) gap theta = tau) ∧
    (∀ {L vg : ℝ}, 0 < L → 0 < vg → 0 < opticalPropagationTime L vg) := by
  exact ⟨fun htau htheta hgap => parityLifetime_mono_gap htau htheta hgap,
    fun htau => parityLifetime_ratio_formula htau,
    calibratedTau0_reproduces,
    fun hL hvg => opticalPropagationTime_pos hL hvg⟩

end InfoGeometry.GrandUnification.TetronParityLifetimeBridge
