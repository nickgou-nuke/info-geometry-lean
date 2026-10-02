import InfoGeometry.Detector.AmariLegendreCore
import InfoGeometry.Geometry.BinaryLegendreEntropyFlow
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open scoped Topology

namespace InfoGeometry.Epistemology.EpistemicGradientFlow

open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Analysis.LogOddsSimplexGeometry
open InfoGeometry.Probability.SimplexQuadraticResponse
open InfoGeometry.Probability.BinaryAitchisonMoments
open InfoGeometry.Geometry.BinaryLegendreEntropyFlow
open InfoGeometry.Detector.AmariLegendreCore
open Filter

theorem logistic_quarter_lipschitz (first second : ℝ) :
    |logistic second - logistic first| ≤ (1 / 4 : ℝ) * |second - first| := by
  have bound : ∀ parameter ∈ (Set.univ : Set ℝ), ‖deriv logistic parameter‖ ≤ (1 / 4 : ℝ) := by
    intro parameter _
    rw [deriv_logistic, Real.norm_eq_abs, abs_of_pos (fisherExp_pos parameter)]
    exact binary_variance_peak _
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun parameter _ => (hasDerivAt_logistic parameter).differentiableAt)
      bound (Set.mem_univ first) (Set.mem_univ second)

theorem midpoint_entropy_quadratic_bound (parameter : ℝ) :
    0 ≤ midpointBregman (logistic parameter) ∧
      midpointBregman (logistic parameter) ≤ parameter ^ 2 / 4 := by
  refine ⟨midpointBregman_nonneg (logistic_mem_Ioo parameter), ?_⟩
  have contact := fenchelGap_contact parameter
  have reverse_gap := fenchel_gap_nonnegative parameter (1 / 2) (by constructor <;> norm_num)
  change 0 ≤ fenchelGap parameter midpoint at reverse_gap
  unfold fenchelGap at contact reverse_gap
  rw [negativeEntropy_midpoint] at reverse_gap
  have upper : midpointBregman (logistic parameter) ≤ parameter * (logistic parameter - 1 / 2) := by
    rw [midpointBregman_eq_negativeEntropy_add_log_two]
    unfold InfoGeometry.Canonical.AmariBinarySimplexBridge.midpoint at reverse_gap
    nlinarith
  have lipschitz := logistic_quarter_lipschitz 0 parameter
  norm_num [logistic] at lipschitz
  have product_bound := mul_le_mul_of_nonneg_left lipschitz (abs_nonneg parameter)
  calc
    midpointBregman (logistic parameter) ≤ parameter * (logistic parameter - 1 / 2) := upper
    _ ≤ |parameter * (logistic parameter - 1 / 2)| := le_abs_self _
    _ = |parameter| * |logistic parameter - 1 / 2| := abs_mul _ _
    _ ≤ |parameter| * ((1 / 4) * |parameter|) := product_bound
    _ = parameter ^ 2 / 4 := by rw [mul_left_comm, ← pow_two, sq_abs]; ring

def relativeEntropy (initial time : ℝ) : ℝ :=
  midpointBregman (entropyRelaxation initial time)

theorem relativeEntropy_eq_binary_kl (initial time : ℝ) :
    relativeEntropy initial time =
      InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence
        (entropyRelaxation initial time) (1 / 2) +
      InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence
        (1 - entropyRelaxation initial time) (1 / 2) := by
  have identity := fenchel_gap_eq_binary_kl 0 (entropyRelaxation initial time)
    (entropyRelaxation_mem_Ioo initial time)
  norm_num [fenchelGap, massieu, logistic] at identity
  unfold relativeEntropy
  rw [midpointBregman_eq_negativeEntropy_add_log_two]
  linarith

theorem hasDerivAt_relativeEntropy (initial time : ℝ) :
    HasDerivAt (relativeEntropy initial)
      (-fisherExp (initial * Real.exp (-time)) * (initial * Real.exp (-time)) ^ 2) time := by
  have derivative := ((hasDerivAt_negativeEntropy (entropyRelaxation_mem_Ioo initial time)).sub_const
    (negativeEntropy midpoint)).comp time (hasDerivAt_entropyRelaxation initial time)
  convert derivative using 1
  unfold entropyGradientField entropyRelaxation
  rw [logit_logistic]
  unfold fisherExp
  ring

theorem relativeEntropy_dissipation (initial time : ℝ) :
    deriv (relativeEntropy initial) time =
      -fisherMix (entropyRelaxation initial time) * (deriv (entropyRelaxation initial) time) ^ 2 := by
  rw [(hasDerivAt_relativeEntropy initial time).deriv,
    (hasDerivAt_entropyRelaxation initial time).deriv]
  have interior := entropyRelaxation_mem_Ioo initial time
  unfold entropyGradientField fisherMix entropyRelaxation at *
  rw [logit_logistic]
  unfold fisherExp
  field_simp [interior.1.ne', (sub_pos.mpr interior.2).ne']

theorem relativeEntropy_antitone (initial : ℝ) : Antitone (relativeEntropy initial) := by
  apply antitone_of_deriv_nonpos
  · intro time
    exact (hasDerivAt_relativeEntropy initial time).differentiableAt
  · intro time
    rw [(hasDerivAt_relativeEntropy initial time).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (fisherExp_pos _).le) (sq_nonneg _)

theorem relativeEntropy_exponential_bound (initial time : ℝ) :
    0 ≤ relativeEntropy initial time ∧
      relativeEntropy initial time ≤ initial ^ 2 / 4 * Real.exp (-2 * time) := by
  have bound := midpoint_entropy_quadratic_bound (initial * Real.exp (-time))
  refine ⟨bound.1, bound.2.trans_eq ?_⟩
  rw [mul_pow, pow_two (Real.exp (-time)), ← Real.exp_add]
  rw [show -time + -time = -2 * time by ring]
  ring

theorem relaxation_tendsto_midpoint (initial : ℝ) :
    Tendsto (entropyRelaxation initial) atTop (𝓝 (1 / 2 : ℝ)) := by
  have coordinate : Tendsto (fun time : ℝ => initial * Real.exp (-time)) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
  have limit := (hasDerivAt_logistic 0).continuousAt.tendsto.comp coordinate
  change Tendsto (entropyRelaxation initial) atTop (𝓝 (logistic 0)) at limit
  convert limit using 1
  norm_num [logistic]

theorem relativeEntropy_tendsto_zero (initial : ℝ) :
    Tendsto (relativeEntropy initial) atTop (𝓝 0) := by
  have interior : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have continuous := ((hasDerivAt_negativeEntropy interior).sub_const
    (negativeEntropy midpoint)).continuousAt
  have limit := continuous.tendsto.comp (relaxation_tendsto_midpoint initial)
  change Tendsto (relativeEntropy initial) atTop
    (𝓝 (negativeEntropy midpoint - negativeEntropy midpoint)) at limit
  simpa only [sub_self] using limit

end InfoGeometry.Epistemology.EpistemicGradientFlow
