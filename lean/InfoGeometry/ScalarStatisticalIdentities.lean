import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.ScalarStatisticalIdentities

def exponentialSeparation (initial rate time : ℝ) : ℝ :=
  initial * Real.exp (rate * time)

theorem exponentialSeparation_pos (initial rate time : ℝ)
    (positive : 0 < initial) : 0 < exponentialSeparation initial rate time :=
  mul_pos positive (Real.exp_pos _)

theorem exponentialSeparation_strictMono (initial rate : ℝ)
    (initial_positive : 0 < initial) (rate_positive : 0 < rate) :
    StrictMono (exponentialSeparation initial rate) := by
  intro earlier later ordered
  exact mul_lt_mul_of_pos_left
    (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left ordered rate_positive)) initial_positive

def odds (probability : ℝ) : ℝ := probability / (1 - probability)

def probabilityFromOdds (weight : ℝ) : ℝ := weight / (1 + weight)

theorem odds_pos (probability : ℝ) (interior : probability ∈ Set.Ioo (0 : ℝ) 1) :
    0 < odds probability :=
  div_pos interior.1 (sub_pos.mpr interior.2)

theorem probabilityFromOdds_mem (weight : ℝ) (positive : 0 < weight) :
    probabilityFromOdds weight ∈ Set.Ioo (0 : ℝ) 1 := by
  have denominator_positive : 0 < 1 + weight := by linarith
  constructor
  · exact div_pos positive denominator_positive
  · unfold probabilityFromOdds
    apply (div_lt_iff₀ denominator_positive).mpr
    linarith

theorem probabilityFromOdds_odds (probability : ℝ) (regular : 1 - probability ≠ 0) :
    probabilityFromOdds (odds probability) = probability := by
  unfold probabilityFromOdds odds
  have denominator : 1 + probability / (1 - probability) = 1 / (1 - probability) := by
    field_simp [regular]
    <;> ring
  rw [denominator]
  simpa only [div_one] using div_div_div_cancel_right₀ regular probability (1 : ℝ)

theorem odds_probabilityFromOdds (weight : ℝ) (regular : 1 + weight ≠ 0) :
    odds (probabilityFromOdds weight) = weight := by
  unfold odds probabilityFromOdds
  have denominator : 1 - weight / (1 + weight) = 1 / (1 + weight) := by
    field_simp [regular]
    <;> ring
  rw [denominator]
  simpa only [div_one] using div_div_div_cancel_right₀ regular weight (1 : ℝ)

def squareRootOdds (calibration probability : ℝ) : ℝ :=
  calibration * Real.sqrt (odds probability)

theorem squareRootOdds_scaling (calibration probability scale : ℝ)
    (scale_nonnegative : 0 ≤ scale) (odds_nonnegative : 0 ≤ odds probability) :
    squareRootOdds calibration (probabilityFromOdds (scale ^ 2 * odds probability)) =
      scale * squareRootOdds calibration probability := by
  have regular : 1 + scale ^ 2 * odds probability ≠ 0 := by
    have product_nonnegative := mul_nonneg (sq_nonneg scale) odds_nonnegative
    linarith
  unfold squareRootOdds
  rw [odds_probabilityFromOdds _ regular, Real.sqrt_mul (sq_nonneg scale),
    Real.sqrt_sq scale_nonnegative]
  ring

theorem inverse_information_scaling (information variance samples : ℝ)
    (inverse_relation : variance * information = 1) (samples_ne : samples ≠ 0) :
    (variance / samples) * (samples * information) = 1 := by
  calc
    (variance / samples) * (samples * information) =
        (variance / samples * samples) * information := (mul_assoc _ _ _).symm
    _ = variance * information := by rw [div_mul_cancel₀ _ samples_ne]
    _ = 1 := inverse_relation

theorem equal_moments_fano_ratio (mean variance : ℝ)
    (equal_moments : variance = mean) (mean_ne : mean ≠ 0) : variance / mean = 1 := by
  rw [equal_moments, div_self mean_ne]

theorem equal_moments_relative_fluctuation (mean variance : ℝ)
    (equal_moments : variance = mean) :
    Real.sqrt variance / mean = 1 / Real.sqrt mean := by
  rw [equal_moments]
  exact Real.sqrt_div_self'

def rootScale (coefficient samples : ℝ) : ℝ := coefficient / Real.sqrt samples

theorem rootScale_mul (coefficient samples scale : ℝ) (scale_nonnegative : 0 ≤ scale) :
    rootScale coefficient (scale * samples) =
      (Real.sqrt scale)⁻¹ * rootScale coefficient samples := by
  unfold rootScale
  rw [Real.sqrt_mul scale_nonnegative]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem rootScale_antitoneOn (coefficient : ℝ) (nonnegative : 0 ≤ coefficient) :
    AntitoneOn (rootScale coefficient) (Set.Ioi 0) := by
  intro smaller smaller_positive larger _ ordered
  exact div_le_div_of_nonneg_left nonnegative
    (Real.sqrt_pos.mpr smaller_positive) (Real.sqrt_le_sqrt ordered)

def WithinRadius (estimate center radius : ℝ) : Prop :=
  (estimate - center) ^ 2 ≤ radius ^ 2

theorem zero_radius_iff (estimate center : ℝ) :
    WithinRadius estimate center 0 ↔ estimate = center := by
  unfold WithinRadius
  constructor
  · intro bounded
    have square_zero : (estimate - center) ^ 2 = 0 := by
      exact le_antisymm (by simpa using bounded) (sq_nonneg _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp square_zero)
  · intro equal
    subst estimate
    simp

def standardizedCoordinate (value mean variance : ℝ) : ℝ :=
  (value - mean) / Real.sqrt variance

theorem simultaneous_linear_scaling (value mean variance samples : ℝ)
    (samples_positive : 0 < samples) :
    standardizedCoordinate (samples * value) (samples * mean) (samples * variance) =
      Real.sqrt samples * standardizedCoordinate value mean variance := by
  have root_ne : Real.sqrt samples ≠ 0 := (Real.sqrt_pos.mpr samples_positive).ne'
  have numerator : samples * (value - mean) =
      Real.sqrt samples * (Real.sqrt samples * (value - mean)) := by
    rw [← mul_assoc, Real.mul_self_sqrt samples_positive.le]
  unfold standardizedCoordinate
  rw [← mul_sub, Real.sqrt_mul samples_positive.le, numerator,
    mul_div_mul_left _ _ root_ne]
  ring

theorem deterministic_positive_scaling_invariant (value mean variance scale : ℝ)
    (scale_positive : 0 < scale) :
    standardizedCoordinate (scale * value) (scale * mean) (scale ^ 2 * variance) =
      standardizedCoordinate value mean variance := by
  unfold standardizedCoordinate
  rw [Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq scale_positive.le, ← mul_sub]
  exact mul_div_mul_left _ _ scale_positive.ne'

theorem simultaneous_linear_scaling_not_invariant :
    standardizedCoordinate 4 0 4 ≠ standardizedCoordinate 1 0 1 := by
  norm_num [standardizedCoordinate]

end InfoGeometry.ScalarStatisticalIdentities
