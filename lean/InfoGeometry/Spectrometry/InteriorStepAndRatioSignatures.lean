/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.InteriorLogSlope
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Real.Sqrt

/-!
# Interior step projection and adjacent-ratio signatures

`InteriorLogSlope.lean` supplies the shared finite weighted-fit definitions.

The concrete regression uses exactly cartridges 2 through 8 with equal
weights and a free intercept. A positive log step is `+delta` at cartridges
4 through 8. It shifts the fitted log slope by `+5*delta/28`; the attenuation
coefficient in `intercept - mu * position` shifts by `-5*delta/28`.

These are exact algebraic statements about a supplied step model. They do not
identify an experimental cause, estimate uncertainty, select a change point,
or establish that multiplying the measured data is physically warranted.
-/

namespace InfoGeometry.Spectrometry.InteriorStepAndRatioSignatures

open scoped BigOperators
open InteriorLogSlope

noncomputable section

def position : Fin 7 → ℝ := ![2, 3, 4, 5, 6, 7, 8]

def uniformWeight : Fin 7 → ℝ := fun _ => 1

/-- One exactly on cartridges 4 through 8, zero on cartridges 2 and 3. -/
def stepAtFour : Fin 7 → ℝ := ![0, 0, 1, 1, 1, 1, 1]

def stepProfile (intercept mu delta : ℝ) : Fin 7 → ℝ :=
  fun j => intercept - mu * position j + delta * stepAtFour j

def fittedLog (profile : Fin 7 → ℝ) : Fin 7 → ℝ :=
  fun j => weightedMean uniformWeight profile +
    weightedSlope uniformWeight position profile *
      (position j - weightedMean uniformWeight position)

def fittedResidual (profile : Fin 7 → ℝ) : Fin 7 → ℝ :=
  fun j => profile j - fittedLog profile j

theorem position_mean : weightedMean uniformWeight position = 5 := by
  norm_num [weightedMean, uniformWeight, position, Fin.sum_univ_succ]

theorem position_denominator : slopeDenominator uniformWeight position = 28 := by
  unfold slopeDenominator
  rw [position_mean]
  norm_num [uniformWeight, position, Fin.sum_univ_succ]

theorem step_mean : weightedMean uniformWeight stepAtFour = (5 / 7 : ℝ) := by
  norm_num [weightedMean, uniformWeight, stepAtFour, Fin.sum_univ_succ]

theorem step_log_slope :
    weightedSlope uniformWeight position stepAtFour = (5 / 28 : ℝ) := by
  unfold weightedSlope
  rw [position_mean, position_denominator]
  norm_num [uniformWeight, position, stepAtFour, Fin.sum_univ_succ]

theorem stepProfile_mean (intercept mu delta : ℝ) :
    weightedMean uniformWeight (stepProfile intercept mu delta) =
      intercept - 5 * mu + (5 / 7 : ℝ) * delta := by
  norm_num [weightedMean, uniformWeight, position, stepAtFour, stepProfile,
    Fin.sum_univ_succ] <;> ring

/-- The signed log slope, not the positive attenuation parameter. -/
theorem stepProfile_log_slope (intercept mu delta : ℝ) :
    weightedSlope uniformWeight position (stepProfile intercept mu delta) =
      -mu + (5 / 28 : ℝ) * delta := by
  unfold weightedSlope
  rw [position_mean, position_denominator]
  norm_num [uniformWeight, position, stepAtFour, stepProfile,
    Fin.sum_univ_succ] <;> ring

/-- For the convention `log intensity = intercept - mu * position`. -/
theorem stepProfile_fitted_attenuation (intercept mu delta : ℝ) :
    -weightedSlope uniformWeight position (stepProfile intercept mu delta) =
      mu - (5 / 28 : ℝ) * delta := by
  rw [stepProfile_log_slope]
  ring

theorem stepProfile_fittedLog (intercept mu delta : ℝ) (j : Fin 7) :
    fittedLog (stepProfile intercept mu delta) j =
      intercept - mu * position j +
        delta * ((5 / 7 : ℝ) + (5 / 28 : ℝ) * (position j - 5)) := by
  unfold fittedLog
  rw [stepProfile_mean, stepProfile_log_slope, position_mean]
  ring

/-- The residual of the actual finite-sum OLS coefficient formula. -/
theorem stepProfile_residual (intercept mu delta : ℝ) (j : Fin 7) :
    fittedResidual (stepProfile intercept mu delta) j =
      delta * (stepAtFour j - (5 / 7 : ℝ) -
        (5 / 28 : ℝ) * (position j - 5)) := by
  unfold fittedResidual
  rw [stepProfile_fittedLog]
  unfold stepProfile
  ring

/-- The explicit seven normalized residuals in physical cartridge order. -/
def stepResidualCoefficient : Fin 7 → ℝ :=
  ![-5 / 28, -10 / 28, 13 / 28, 8 / 28, 3 / 28, -2 / 28, -7 / 28]

theorem stepProfile_residual_vector (intercept mu delta : ℝ) (j : Fin 7) :
    fittedResidual (stepProfile intercept mu delta) j = delta * stepResidualCoefficient j := by
  rw [stepProfile_residual]
  fin_cases j <;>
    norm_num [stepAtFour, position, stepResidualCoefficient] <;> ring

theorem stepResidual_sum_zero : ∑ j, stepResidualCoefficient j = 0 := by
  norm_num [stepResidualCoefficient, Fin.sum_univ_succ]

theorem stepResidual_centered_cross_zero :
    ∑ j, (position j - 5) * stepResidualCoefficient j = 0 := by
  norm_num [stepResidualCoefficient, position, Fin.sum_univ_succ]

theorem stepProfile_residual_sum_sq (intercept mu delta : ℝ) :
    (∑ j, fittedResidual (stepProfile intercept mu delta) j ^ 2) =
      (15 / 28 : ℝ) * delta ^ 2 := by
  simp_rw [stepProfile_residual_vector]
  norm_num [stepResidualCoefficient, Fin.sum_univ_succ] <;> ring

/-- Exact Pythagorean identity proves least-squares optimality for this
concrete step family, rather than merely naming a coefficient an OLS slope. -/
theorem stepProfile_loss_pythagoras
    (intercept mu delta otherIntercept otherSlope : ℝ) :
    (∑ j, (stepProfile intercept mu delta j -
      (otherIntercept + otherSlope * position j)) ^ 2) =
      (15 / 28 : ℝ) * delta ^ 2 +
        ∑ j, (fittedLog (stepProfile intercept mu delta) j -
          (otherIntercept + otherSlope * position j)) ^ 2 := by
  simp_rw [stepProfile_fittedLog]
  norm_num [stepProfile, stepAtFour, position, Fin.sum_univ_succ] <;> ring

theorem stepProfile_leastSquares_minimum
    (intercept mu delta otherIntercept otherSlope : ℝ) :
    (∑ j, fittedResidual (stepProfile intercept mu delta) j ^ 2) ≤
      ∑ j, (stepProfile intercept mu delta j -
        (otherIntercept + otherSlope * position j)) ^ 2 := by
  rw [stepProfile_residual_sum_sq,
    stepProfile_loss_pythagoras intercept mu delta otherIntercept otherSlope]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem nonzero_step_not_affine (intercept mu delta : ℝ) (hdelta : delta ≠ 0) :
    ¬ ∃ a b : ℝ, ∀ j, stepProfile intercept mu delta j = a + b * position j := by
  rintro ⟨a, b, h⟩
  have h₂ := h (0 : Fin 7)
  have h₃ := h (1 : Fin 7)
  have h₄ := h (2 : Fin 7)
  norm_num [stepProfile, stepAtFour, position] at h₂ h₃ h₄
  apply hdelta
  linarith

/-- Adding the opposite group step exactly cancels the supplied discontinuity.
This is an algebraic correction, not evidence that the correction is physical. -/
theorem compensating_group_step (intercept mu delta : ℝ) (j : Fin 7) :
    stepProfile intercept mu delta j + delta * (1 - stepAtFour j) =
      (intercept + delta) - mu * position j := by
  unfold stepProfile
  ring

/-- Multiplying only the middle sample divides the preceding adjacent ratio. -/
theorem middle_multiplier_preceding_ratio (left middle factor : ℝ) :
    left / (factor * middle) = (left / middle) / factor := by
  rw [div_div, mul_comm middle factor]

/-- The same middle-sample multiplier multiplies the following ratio. -/
theorem middle_multiplier_following_ratio (middle right factor : ℝ) :
    (factor * middle) / right = factor * (middle / right) := by
  ring

theorem paired_ratio_product_preserved (r s factor : ℝ) (hfactor : factor ≠ 0) :
    (r / factor) * (factor * s) = r * s := by
  field_simp [hfactor] <;> ring

/-- The positive square-root choice equalizes the paired adjacent ratios. -/
theorem positive_multiplier_equalizes_pair (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    r / Real.sqrt (r / s) = Real.sqrt (r / s) * s := by
  have hquot : 0 < r / s := div_pos hr hs
  have hsqrt : 0 < Real.sqrt (r / s) := Real.sqrt_pos.2 hquot
  apply (div_eq_iff hsqrt.ne').mpr
  calc
    r = (r / s) * s := (div_mul_cancel₀ r hs.ne').symm
    _ = Real.sqrt (r / s) ^ 2 * s := by rw [Real.sq_sqrt hquot.le]
    _ = (Real.sqrt (r / s) * s) * Real.sqrt (r / s) := by ring

/-- Multiplying a whole upstream group leaves ratios internal to it unchanged. -/
theorem group_multiplier_internal_ratio (left right factor : ℝ) (hfactor : factor ≠ 0) :
    (factor * left) / (factor * right) = left / right := by
  by_cases hright : right = 0
  · simp [hright]
  · field_simp [hfactor, hright] <;> ring

end
end InfoGeometry.Spectrometry.InteriorStepAndRatioSignatures
