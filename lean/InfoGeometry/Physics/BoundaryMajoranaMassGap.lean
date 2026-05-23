import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Explicit boundary Majorana mass-gap readouts

This file keeps the boundary mass-gap layer scalar and constructive:

* a one-pair Majorana gap is `|λ|`;
* the two-state splitting convention is `2 |λ|`;
* the explicit scalar Pfaffian gap model is `|Pf|`, so `Pf = 0` closes it;
* chiral central charge is `c_- = (N_R - N_L) / 2`;
* chiral CFT pressure and Weyl gap scaling are closed-form definitions.

No Riemann-spectrum theorem, `E₈` representation theorem, or full gravity
theorem is asserted here.
-/

namespace InfoGeometry.Physics.BoundaryMajoranaMassGap

/-! ## 1. Explicit one-pair Majorana gap -/

/-- BdG quasiparticle gap for one Majorana pair with singular value `λ`. -/
def majoranaPairGap (lambda : ℝ) : ℝ :=
  |lambda|

/-- Two-state fermion-parity splitting convention for one Majorana pair. -/
def majoranaPairSplitting (lambda : ℝ) : ℝ :=
  2 * majoranaPairGap lambda

/-- The explicit one-pair gap is nonnegative. -/
theorem majoranaPairGap_nonneg (lambda : ℝ) :
    0 ≤ majoranaPairGap lambda := by
  unfold majoranaPairGap
  exact abs_nonneg lambda

/-- The explicit two-state splitting is twice the BdG gap. -/
theorem majoranaPairSplitting_eq_two_mul_gap (lambda : ℝ) :
    majoranaPairSplitting lambda = 2 * majoranaPairGap lambda :=
  rfl

/-- The one-pair gap vanishes exactly when the singular value vanishes. -/
theorem majoranaPairGap_eq_zero_iff (lambda : ℝ) :
    majoranaPairGap lambda = 0 ↔ lambda = 0 := by
  unfold majoranaPairGap
  exact abs_eq_zero

/-! ## 2. Explicit scalar Pfaffian transition model -/

/-- Scalar Pfaffian gap model: the protected gap readout is `|Pf|`. -/
def pfaffianGap (pfaffian : ℝ) : ℝ :=
  |pfaffian|

/-- The scalar Pfaffian gap is nonnegative. -/
theorem pfaffianGap_nonneg (pfaffian : ℝ) :
    0 ≤ pfaffianGap pfaffian := by
  unfold pfaffianGap
  exact abs_nonneg pfaffian

/-- In the explicit scalar Pfaffian gap model, `Pf = 0` closes the gap. -/
theorem pfaffian_zero_forces_gap_closing {pfaffian : ℝ}
    (hpf : pfaffian = 0) :
    pfaffianGap pfaffian = 0 := by
  rw [hpf]
  simp [pfaffianGap]

/-- The explicit scalar Pfaffian gap vanishes exactly at zero Pfaffian. -/
theorem pfaffianGap_eq_zero_iff (pfaffian : ℝ) :
    pfaffianGap pfaffian = 0 ↔ pfaffian = 0 := by
  unfold pfaffianGap
  exact abs_eq_zero

/-! ## 3. Chiral Majorana central charge bookkeeping -/

/-- Net chiral Majorana count `N_R - N_L`. -/
def netChiralMajorana (rightModes leftModes : ℝ) : ℝ :=
  rightModes - leftModes

/-- Chiral Majorana central charge `c_- = (N_R - N_L)/2`. -/
noncomputable def chiralMajoranaCentralCharge (rightModes leftModes : ℝ) : ℝ :=
  netChiralMajorana rightModes leftModes / 2

/-- Chiral central charge is half the net chiral Majorana count. -/
theorem chiralMajoranaCentralCharge_eq_half_net
    (rightModes leftModes : ℝ) :
    chiralMajoranaCentralCharge rightModes leftModes =
      netChiralMajorana rightModes leftModes / 2 :=
  rfl

/-- If `c_- = 8`, then the net chiral Majorana count is `16`. -/
theorem netChiral_eq_sixteen_of_cMinus_eq_eight
    {rightModes leftModes : ℝ}
    (hE8 : chiralMajoranaCentralCharge rightModes leftModes = 8) :
    netChiralMajorana rightModes leftModes = 16 := by
  unfold chiralMajoranaCentralCharge at hE8
  nlinarith

/-- The `E₈` level-one central-charge condition is `N_R - N_L = 16`. -/
theorem right_minus_left_eq_sixteen_of_cMinus_eq_eight
    {rightModes leftModes : ℝ}
    (hE8 : chiralMajoranaCentralCharge rightModes leftModes = 8) :
    rightModes - leftModes = 16 := by
  exact netChiral_eq_sixteen_of_cMinus_eq_eight hE8

/-! ## 4. Chiral boundary CFT pressure -/

/-- Scalar chiral boundary CFT thermal pressure `π c_- T²/(12v)`. -/
noncomputable def chiralBoundaryThermalPressure
    (cMinus velocity temperature : ℝ) : ℝ :=
  Real.pi * cMinus * temperature ^ 2 / (12 * velocity)

/-- Horizon temperature `T = κ/(2π)`. -/
noncomputable def horizonTemperature (kappa : ℝ) : ℝ :=
  kappa / (2 * Real.pi)

/-- Horizon-pressure readout after substituting `T = κ/(2π)`. -/
noncomputable def chiralBoundaryHorizonPressure
    (cMinus velocity kappa : ℝ) : ℝ :=
  chiralBoundaryThermalPressure cMinus velocity (horizonTemperature kappa)

/-- Horizon-temperature pressure: `P = c_- κ² / (48πv)`. -/
theorem chiralBoundaryHorizonPressure_eq
    (cMinus velocity kappa : ℝ) :
    chiralBoundaryHorizonPressure cMinus velocity kappa =
      cMinus * kappa ^ 2 / (48 * Real.pi * velocity) := by
  unfold chiralBoundaryHorizonPressure chiralBoundaryThermalPressure horizonTemperature
  field_simp [Real.pi_ne_zero]
  ring

/-- For `c_- = 8`, the pressure is `κ²/(6πv)`. -/
theorem chiralBoundaryHorizonPressure_eq_E8
    (velocity kappa : ℝ) :
    chiralBoundaryHorizonPressure 8 velocity kappa =
      kappa ^ 2 / (6 * Real.pi * velocity) := by
  rw [chiralBoundaryHorizonPressure_eq]
  ring

/-! ## 5. Weyl scaling of the boundary gap -/

/-- Weyl scaling of a boundary Majorana gap: `Δ(φ) = exp(-φ) Δ₀`. -/
noncomputable def weylScaledGap (gap0 phi : ℝ) : ℝ :=
  Real.exp (-phi) * gap0

/-- Weyl scaling keeps the gap positive when the reference gap is positive. -/
theorem weylScaledGap_pos {gap0 phi : ℝ}
    (hgap0 : 0 < gap0) :
    0 < weylScaledGap gap0 phi := by
  unfold weylScaledGap
  exact mul_pos (Real.exp_pos _) hgap0

/-- Logarithmic Weyl gap scaling: `log Δ = log Δ₀ - φ`. -/
theorem log_weylScaledGap_eq_log_gap0_sub_phi {gap0 phi : ℝ}
    (hgap0 : 0 < gap0) :
    Real.log (weylScaledGap gap0 phi) = Real.log gap0 - phi := by
  unfold weylScaledGap
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hgap0)]
  rw [Real.log_exp]
  ring

end InfoGeometry.Physics.BoundaryMajoranaMassGap
