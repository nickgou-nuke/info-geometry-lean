import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace InfoGeometry.Detector.CommonScaleReadout

noncomputable section

def readout (singleCoefficient coincidenceCoefficient scale : ℝ) : ℝ :=
  (singleCoefficient * scale) / Real.sqrt (coincidenceCoefficient * scale ^ 2)

theorem sqrt_quadratic_scale (coefficient scale : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient) :
    Real.sqrt (coefficient * scale ^ 2) = Real.sqrt coefficient * |scale| := by
  rw [Real.sqrt_mul coefficient_nonneg, Real.sqrt_sq_eq_abs]

theorem readout_eq (singleCoefficient coincidenceCoefficient scale : ℝ)
    (coefficient_nonneg : 0 ≤ coincidenceCoefficient) (scale_positive : 0 < scale) :
    readout singleCoefficient coincidenceCoefficient scale =
      singleCoefficient / Real.sqrt coincidenceCoefficient := by
  rw [readout, sqrt_quadratic_scale _ _ coefficient_nonneg, abs_of_pos scale_positive]
  exact mul_div_mul_right _ _ scale_positive.ne'

theorem readout_invariant (singleCoefficient coincidenceCoefficient first second : ℝ)
    (coefficient_nonneg : 0 ≤ coincidenceCoefficient)
    (first_positive : 0 < first) (second_positive : 0 < second) :
    readout singleCoefficient coincidenceCoefficient first =
      readout singleCoefficient coincidenceCoefficient second := by
  rw [readout_eq _ _ _ coefficient_nonneg first_positive,
    readout_eq _ _ _ coefficient_nonneg second_positive]

theorem inverse_square_readout
    (volume singleCoefficient coincidenceCoefficient distance offset : ℝ)
    (volume_positive : 0 < volume) (coefficient_nonneg : 0 ≤ coincidenceCoefficient)
    (separation_nonzero : distance + offset ≠ 0) :
    (volume * (singleCoefficient / (distance + offset) ^ 2)) /
        Real.sqrt (volume ^ 2 * (coincidenceCoefficient / (distance + offset) ^ 4)) =
      singleCoefficient / Real.sqrt coincidenceCoefficient := by
  have scale_positive : 0 < volume / (distance + offset) ^ 2 :=
    div_pos volume_positive (sq_pos_of_ne_zero separation_nonzero)
  have numerator : volume * (singleCoefficient / (distance + offset) ^ 2) =
      singleCoefficient * (volume / (distance + offset) ^ 2) := by ring
  have denominator : volume ^ 2 * (coincidenceCoefficient / (distance + offset) ^ 4) =
      coincidenceCoefficient * (volume / (distance + offset) ^ 2) ^ 2 := by
    field_simp
  rw [numerator, denominator]
  exact readout_eq _ _ _ coefficient_nonneg scale_positive

theorem hasFDerivAt_readout_comp
    {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    (scale : Parameter → ℝ) (singleCoefficient coincidenceCoefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coincidenceCoefficient)
    (scale_positive : ∀ parameter, 0 < scale parameter) (point : Parameter) :
    HasFDerivAt (fun parameter => readout singleCoefficient coincidenceCoefficient
      (scale parameter)) (0 : Parameter →L[ℝ] ℝ) point := by
  have constant : (fun parameter =>
      readout singleCoefficient coincidenceCoefficient (scale parameter)) =
      fun _ => singleCoefficient / Real.sqrt coincidenceCoefficient := by
    funext parameter
    exact readout_eq _ _ _ coefficient_nonneg (scale_positive parameter)
  rw [constant]
  exact hasFDerivAt_const _ _

theorem hasDerivAt_readout_path (scale : ℝ → ℝ)
    (singleCoefficient coincidenceCoefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coincidenceCoefficient)
    (scale_positive : ∀ time, 0 < scale time) (time : ℝ) :
    HasDerivAt (fun instant =>
      readout singleCoefficient coincidenceCoefficient (scale instant)) 0 time := by
  simpa using (hasFDerivAt_readout_comp scale singleCoefficient coincidenceCoefficient
    coefficient_nonneg scale_positive time).hasDerivAt

theorem readout_at_zero (singleCoefficient coincidenceCoefficient : ℝ) :
    readout singleCoefficient coincidenceCoefficient 0 = 0 := by
  simp [readout]

theorem readout_neg_scale (singleCoefficient coincidenceCoefficient scale : ℝ) :
    readout singleCoefficient coincidenceCoefficient (-scale) =
      -readout singleCoefficient coincidenceCoefficient scale := by
  simp [readout, mul_neg, neg_div]

end

end InfoGeometry.Detector.CommonScaleReadout
