import InfoGeometry.Spectrometry.AlternatingInformationProjection
import InfoGeometry.Spectrometry.MatrixQuadraticBregman

namespace InfoGeometry.Spectrometry.AlternatingInformationProjection.Tests

open scoped BigOperators Topology
open Filter FixedScaleLeastSquares MatrixFixedScaleLeastSquares MatrixQuadraticBregman
open AitchisonGeometricMedian ThermodynamicTransportPipeline SvdClrEquivalence

noncomputable section

def sample : Matrix (Fin 2) (Fin 2) ℝ := !![1, 3; 2, 4]

example : optimalProfile sample ![1, 2] = ![7 / 5, 2] := by
  funext row
  fin_cases row <;>
    norm_num [sample, optimal_profile_formula, scaleSquareSum, Fin.sum_univ_two]

example : totalLoss sample ![1, 2] (optimalProfile sample ![1, 2]) = 1 / 5 := by
  norm_num [sample, totalLoss, rowLoss, optimal_profile_formula,
    scaleSquareSum, Fin.sum_univ_two]

example : totalLoss sample ![1, 2] ![0, 0] = 30 := by
  norm_num [sample, totalLoss, rowLoss, Fin.sum_univ_two]

example : ∀ profile : Fin 2 → ℝ,
    totalLoss sample ![1, 2] profile = 1 / 5 ↔ profile = ![7 / 5, 2] := by
  intro profile
  have optimal : optimalProfile sample ![1, 2] = ![7 / 5, 2] := by
    funext row
    fin_cases row <;>
      norm_num [sample, optimal_profile_formula, scaleSquareSum, Fin.sum_univ_two]
  have residual : totalLoss sample ![1, 2] (optimalProfile sample ![1, 2]) = 1 / 5 := by
    rw [optimal]
    norm_num [sample, totalLoss, rowLoss, Fin.sum_univ_two]
  have characterization := total_loss_eq_minimum_iff sample ![1, 2] profile
    (by norm_num [scaleSquareSum, Fin.sum_univ_two])
  rw [residual, optimal] at characterization
  exact characterization

example : totalLoss sample 0 ![0, 0] = totalLoss sample 0 ![1, 1] := by
  rw [total_loss_zero_scales, total_loss_zero_scales]

example (observed : Matrix (Fin 0) (Fin 2) ℝ) (scales : Fin 2 → ℝ)
    (profile : Fin 0 → ℝ) : totalLoss observed scales profile = 0 := by
  simp [totalLoss]

example (observed : Matrix (Fin 2) (Fin 0) ℝ) (scales : Fin 0 → ℝ)
    (profile : Fin 2 → ℝ) : totalLoss observed scales profile = 0 := by
  simp [totalLoss, rowLoss]

example (profile : Fin 2 → ℝ) :
    totalLoss (responseMatrix profile ![1, 2]) ![1, 2]
      (optimalProfile (responseMatrix profile ![1, 2]) ![1, 2]) = 0 := by
  rw [optimal_profile_exact _ _ (by norm_num [scaleSquareSum, Fin.sum_univ_two])]
  simp [totalLoss, rowLoss, responseMatrix, Matrix.vecMulVec_apply]

example : totalLoss sample ![2, 4] ![7 / 10, 1] = totalLoss sample ![1, 2] ![7 / 5, 2] := by
  convert total_loss_rescale sample ![1, 2] ![7 / 5, 2] 2 (by norm_num) using 1
  norm_num [totalLoss, rowLoss, Fin.sum_univ_two]

example : entrywiseCanonicalDivergence sample (reconstruction sample ![1, 2]) = 1 / 5 := by
  rw [entrywise_canonical_divergence_eq_squared_distance]
  change totalLoss sample ![1, 2] (optimalProfile sample ![1, 2]) = 1 / 5
  norm_num [sample, totalLoss, rowLoss, optimal_profile_formula,
    scaleSquareSum, Fin.sum_univ_two]

def oneRow : Matrix (Fin 1) (Fin 2) ℝ := fun _ => ![1, 3]

theorem constant_sequence_satisfies_block_contracts :
    (∀ step : ℕ, (fun _row : Fin 1 => (2 : ℝ)) =
      profileProjectionStep oneRow ((fun _step : ℕ => (![1, 1] : Fin 2 → ℝ)) step)) ∧
    (∀ step : ℕ,
      totalLoss oneRow ((fun _step : ℕ => (![1, 1] : Fin 2 → ℝ)) (step + 1)) (fun _ => 2) ≤
        totalLoss oneRow ![1, 1] (fun _ => 2)) := by
  constructor
  · intro step
    funext row
    norm_num [profileProjectionStep, oneRow, optimal_profile_formula,
      scaleSquareSum, Fin.sum_univ_two]
  · intro step
    exact le_rfl

theorem constant_sequence_converges_to_two :
    Tendsto (fun _step : ℕ => totalLoss oneRow ![1, 1] (fun _ => 2)) atTop (𝓝 2) := by
  have converges := projection_loss_sequence_converges oneRow
    (fun _step => ![1, 1]) (fun _step _row => 2)
    (fun _step => by norm_num [scaleSquareSum, Fin.sum_univ_two])
    constant_sequence_satisfies_block_contracts.1 constant_sequence_satisfies_block_contracts.2
  have loss : totalLoss oneRow ![1, 1] (fun _ => 2) = 2 := by
    norm_num [oneRow, totalLoss, rowLoss, Fin.sum_univ_two]
  simpa only [loss, ciInf_const] using converges

theorem sequence_infimum_can_exceed_joint_loss :
    totalLoss oneRow ![1, 3] (fun _ => 1) <
      ⨅ _step : ℕ, totalLoss oneRow ![1, 1] (fun _ => 2) := by
  norm_num [oneRow, totalLoss, rowLoss, Fin.sum_univ_two]

def saddleMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 1]

theorem exact_block_minimizers_need_not_be_joint_minimizers :
    optimalProfile saddleMatrix ![0, 1] = ![0, 1] ∧
    optimalProfile saddleMatrix.transpose ![0, 1] = ![0, 1] ∧
    totalLoss saddleMatrix ![1, 0] ![2, 0] < totalLoss saddleMatrix ![0, 1] ![0, 1] := by
  refine ⟨?_, ?_, ?_⟩
  · funext row
    fin_cases row <;>
      norm_num [saddleMatrix, optimal_profile_formula, scaleSquareSum, Fin.sum_univ_two]
  · funext acquisition
    fin_cases acquisition <;>
      norm_num [saddleMatrix, Matrix.transpose_apply, optimal_profile_formula,
        scaleSquareSum, Fin.sum_univ_two]
  · norm_num [saddleMatrix, totalLoss, rowLoss, Fin.sum_univ_two]

def logTwoCenter : aitchisonSpace 2 :=
  ⟨WithLp.toLp 2 ![Real.log 2, -Real.log 2], by
    change (∑ acquisition : Fin 2, (![Real.log 2, -Real.log 2]) acquisition) = 0
    simp [Fin.sum_univ_two]⟩

theorem log_two_center_scales : acquisitionScales logTwoCenter = ![2, 1 / 2] := by
  funext acquisition
  fin_cases acquisition <;>
    simp [acquisitionScales, logTwoCenter, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem centered_proposal_can_increase_loss :
    totalLoss (fun _row : Fin 1 => (![1, 1] : Fin 2 → ℝ))
        (acquisitionScales (0 : aitchisonSpace 2)) (fun _ => 1) <
      totalLoss (fun _row : Fin 1 => (![1, 1] : Fin 2 → ℝ))
        (acquisitionScales logTwoCenter) (fun _ => 1) := by
  rw [log_two_center_scales]
  norm_num [totalLoss, rowLoss, acquisitionScales, Fin.sum_univ_two]

theorem centered_proposal_can_increase_profiled_loss :
    centeredProfileLoss (fun _row : Fin 1 => (![1, 1] : Fin 2 → ℝ)) 0 <
      centeredProfileLoss (fun _row : Fin 1 => (![1, 1] : Fin 2 → ℝ)) logTwoCenter := by
  unfold centeredProfileLoss
  rw [log_two_center_scales]
  norm_num [totalLoss, rowLoss, acquisitionScales, optimal_profile_formula,
    scaleSquareSum, Fin.sum_univ_two]

example : guardedCenterStep (fun _row : Fin 1 => (![1, 1] : Fin 2 → ℝ))
    0 logTwoCenter = 0 := by
  unfold guardedCenterStep
  rw [log_two_center_scales]
  norm_num [centeredProfileLoss, totalLoss, rowLoss, acquisitionScales,
    optimal_profile_formula, scaleSquareSum, Fin.sum_univ_two]

example (observed : Matrix (Fin 2) (Fin 2) ℝ) (current : aitchisonSpace 2) :
    guardedCenterStep observed current current = current := by
  simp [guardedCenterStep, centeredProfileLoss]

example (observed : Matrix (Fin 2) (Fin 2) ℝ)
    (propose : ℕ → aitchisonSpace 2 → aitchisonSpace 2)
    (initial : aitchisonSpace 2) :
    Tendsto (fun step => centeredProfileLoss observed
      (guardedCenterIterate observed propose initial step)) atTop
      (𝓝 (⨅ step, centeredProfileLoss observed
        (guardedCenterIterate observed propose initial step))) :=
  guarded_losses_converge_to_sequence_infimum observed propose initial (by norm_num)

end

end InfoGeometry.Spectrometry.AlternatingInformationProjection.Tests
