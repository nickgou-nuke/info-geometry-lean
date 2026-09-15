import InfoGeometry.Detector.AmariLegendreCore
import InfoGeometry.Detector.AmariHessianDependency

noncomputable section

namespace InfoGeometry.Detector.AmariHessianDuality

open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Analysis.LogOddsSimplexGeometry
open InfoGeometry.Probability.SimplexQuadraticResponse
open InfoGeometry.Detector.AmariLegendreCore

def norm_single (coefficient efficiency : ℝ) : ℝ :=
  response 1 coefficient efficiency

def odds_ratio_chi (coefficient efficiency : ℝ) : ℝ :=
  coefficient * efficiency / (1 - coefficient * efficiency)

def partition_argument (coefficient efficiency : ℝ) : ℝ :=
  1 + odds_ratio_chi coefficient efficiency

def naturalParameter (coefficient efficiency : ℝ) : ℝ :=
  logit (coefficient * efficiency)

def expectation_eta (coefficient efficiency : ℝ) : ℝ :=
  logistic (naturalParameter coefficient efficiency)

def fisher_metric (coefficient efficiency : ℝ) : ℝ :=
  fisherExp (naturalParameter coefficient efficiency)

theorem norm_single_eq (coefficient efficiency : ℝ) :
    norm_single coefficient efficiency = efficiency * (1 - coefficient * efficiency) := by
  unfold norm_single response
  ring

theorem partition_argument_simplification (coefficient efficiency : ℝ)
    (regular : 1 - coefficient * efficiency ≠ 0) :
    partition_argument coefficient efficiency = 1 / (1 - coefficient * efficiency) := by
  unfold partition_argument odds_ratio_chi
  field_simp [regular]
  ring

theorem exp_naturalParameter (coefficient efficiency : ℝ)
    (interior : coefficient * efficiency ∈ Set.Ioo (0 : ℝ) 1) :
    Real.exp (naturalParameter coefficient efficiency) = odds_ratio_chi coefficient efficiency := by
  exact Real.exp_log (div_pos interior.1 (sub_pos.mpr interior.2))

theorem massieu_naturalParameter (coefficient efficiency : ℝ)
    (interior : coefficient * efficiency ∈ Set.Ioo (0 : ℝ) 1) :
    massieu (naturalParameter coefficient efficiency) =
      -Real.log (1 - coefficient * efficiency) := by
  unfold massieu
  rw [exp_naturalParameter coefficient efficiency interior]
  change Real.log (partition_argument coefficient efficiency) = _
  rw [partition_argument_simplification coefficient efficiency (sub_pos.mpr interior.2).ne']
  simp

theorem expectation_eta_eq (coefficient efficiency : ℝ)
    (interior : coefficient * efficiency ∈ Set.Ioo (0 : ℝ) 1) :
    expectation_eta coefficient efficiency = coefficient * efficiency :=
  logistic_logit interior

theorem hessian_is_single_response (coefficient efficiency : ℝ)
    (interior : coefficient * efficiency ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (deriv massieu) (naturalParameter coefficient efficiency) =
      coefficient * norm_single coefficient efficiency := by
  rw [deriv2_massieu, naturalParameter, fisherExp_logit interior, norm_single_eq]
  ring

theorem fisher_metric_is_single_photopeak (coefficient efficiency : ℝ)
    (interior : coefficient * efficiency ∈ Set.Ioo (0 : ℝ) 1) :
    fisher_metric coefficient efficiency = coefficient * norm_single coefficient efficiency := by
  rw [fisher_metric, ← deriv2_massieu]
  exact hessian_is_single_response coefficient efficiency interior

theorem fisher_metric_positive (coefficient efficiency : ℝ) :
    0 < fisher_metric coefficient efficiency := fisherExp_pos _

theorem fisher_metric_le_quarter (coefficient efficiency : ℝ) :
    fisher_metric coefficient efficiency ≤ 1 / 4 :=
  binary_variance_peak _

theorem fisher_metric_eq_quarter_iff (coefficient efficiency : ℝ)
    (interior : coefficient * efficiency ∈ Set.Ioo (0 : ℝ) 1) :
    fisher_metric coefficient efficiency = 1 / 4 ↔ coefficient * efficiency = 1 / 2 := by
  rw [fisher_metric, naturalParameter, fisherExp_logit interior]
  constructor
  · intro maximum
    nlinarith [sq_nonneg (coefficient * efficiency - 1 / 2)]
  · intro balance
    rw [balance]
    norm_num

theorem maximum_fisher_info_at_summit (coefficient : ℝ) (nonzero : coefficient ≠ 0) :
    fisher_metric coefficient (1 / (2 * coefficient)) = 1 / 4 := by
  have balance : coefficient * (1 / (2 * coefficient)) = 1 / 2 := by
    field_simp
  have interior : coefficient * (1 / (2 * coefficient)) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [balance]
    constructor <;> norm_num
  exact (fisher_metric_eq_quarter_iff coefficient _ interior).mpr balance

theorem hasDerivAt_naturalParameter (coefficient efficiency : ℝ)
    (interior : coefficient * efficiency ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (naturalParameter coefficient)
      (fisherMix (coefficient * efficiency) * coefficient) efficiency := by
  simpa only [mul_one] using
    (hasDerivAt_logit interior).comp efficiency ((hasDerivAt_id efficiency).const_mul coefficient)

theorem fisher_efficiency_pullback (coefficient efficiency : ℝ)
    (interior : coefficient * efficiency ∈ Set.Ioo (0 : ℝ) 1) :
    fisher_metric coefficient efficiency * (deriv (naturalParameter coefficient) efficiency) ^ 2 =
      coefficient ^ 2 * fisherMix (coefficient * efficiency) := by
  rw [(hasDerivAt_naturalParameter coefficient efficiency interior).deriv,
    fisher_metric, naturalParameter, fisherExp_logit interior]
  unfold fisherMix
  field_simp [interior.1.ne', (sub_pos.mpr interior.2).ne']

theorem singles_at_boundary (coefficient : ℝ) (nonzero : coefficient ≠ 0) :
    norm_single coefficient (1 / coefficient) = 0 := by
  rw [norm_single_eq]
  field_simp
  ring

theorem no_finite_natural_parameter_at_boundary :
    ¬ ∃ parameter : ℝ, logistic parameter = 1 := by
  rintro ⟨parameter, boundary⟩
  have upper := (logistic_mem_Ioo parameter).2
  linarith

end InfoGeometry.Detector.AmariHessianDuality
