import InfoGeometry.Probability.DetectorAnscombeMadelungRegistration
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace InfoGeometry.NuclearReactions.FoilAlignment

open InfoGeometry.Probability.DetectorAnscombeMadelungRegistration

noncomputable section

def inverseFourthRoot (coincidence : ℝ) : ℝ :=
  1 / Real.sqrt (Real.sqrt coincidence)

def fittedIntercept (slope virtualDepth offset : ℝ) : ℝ :=
  slope * combinedOffset offset virtualDepth

def offsetFromFit (slope intercept virtualDepth : ℝ) : ℝ :=
  intercept / slope - virtualDepth

theorem inverse_fourth_root_of_inverse_fourth_power (coordinate : ℝ)
    (coordinate_pos : 0 < coordinate) :
    inverseFourthRoot (1 / coordinate ^ 4) = coordinate := by
  have power_identity : coordinate ^ 4 = (coordinate ^ 2) ^ 2 := by ring
  unfold inverseFourthRoot
  rw [power_identity, Real.sqrt_div (by norm_num), Real.sqrt_one,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg coordinate),
    Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq_eq_abs, abs_of_pos coordinate_pos]
  simp

theorem fourth_root_distance_law
    (coincidence slope distance virtualDepth offset : ℝ)
    (coordinate_pos : 0 < slope * (distance + combinedOffset offset virtualDepth))
    (coincidence_law : coincidence = 1 / (slope * (distance + combinedOffset offset virtualDepth)) ^ 4) :
    inverseFourthRoot coincidence = slope * distance + fittedIntercept slope virtualDepth offset := by
  rw [coincidence_law, inverse_fourth_root_of_inverse_fourth_power _ coordinate_pos]
  unfold fittedIntercept
  ring

theorem offset_from_fit_exact (slope virtualDepth offset : ℝ) (slope_ne : slope ≠ 0) :
    offsetFromFit slope (fittedIntercept slope virtualDepth offset) virtualDepth = offset := by
  unfold offsetFromFit fittedIntercept combinedOffset
  field_simp [slope_ne]
  ring

theorem normalized_intercept_shift
    (firstSlope secondSlope virtualDepth firstOffset secondOffset : ℝ)
    (first_slope_ne : firstSlope ≠ 0) (second_slope_ne : secondSlope ≠ 0) :
    fittedIntercept secondSlope virtualDepth secondOffset / secondSlope -
        fittedIntercept firstSlope virtualDepth firstOffset / firstSlope = secondOffset - firstOffset := by
  unfold fittedIntercept combinedOffset
  field_simp
  ring

theorem offset_error_exact (slope virtualDepth offset interceptError : ℝ) (slope_ne : slope ≠ 0) :
    offsetFromFit slope (fittedIntercept slope virtualDepth offset + interceptError) virtualDepth - offset =
      interceptError / slope := by
  unfold offsetFromFit fittedIntercept combinedOffset
  field_simp [slope_ne]
  ring

theorem offset_error_bound (slope virtualDepth offset interceptError errorBound : ℝ)
    (slope_ne : slope ≠ 0) (error_bound : |interceptError| ≤ errorBound) :
    |offsetFromFit slope (fittedIntercept slope virtualDepth offset + interceptError) virtualDepth - offset| ≤
      errorBound / |slope| := by
  rw [offset_error_exact _ _ _ _ slope_ne, abs_div]
  exact div_le_div_of_nonneg_right error_bound (abs_nonneg slope)

end

end InfoGeometry.NuclearReactions.FoilAlignment
