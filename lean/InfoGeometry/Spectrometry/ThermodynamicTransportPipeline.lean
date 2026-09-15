import InfoGeometry.Spectrometry.AitchisonGeometricMedian
import InfoGeometry.Spectrometry.FixedScaleLeastSquares

namespace InfoGeometry.Spectrometry.ThermodynamicTransportPipeline

open scoped BigOperators Topology
open Filter SvdClrEquivalence AitchisonGeometricMedian FixedScaleLeastSquares

namespace PipelineDependency

inductive Archetype
  | centeredGeometry
  | exponentiatedScales
  | leastSquaresProjection
  | logMeanInvariance
  | separableModel
  | rankOneExactness
  | iteratePreservation
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | centeredGeometry => {centeredGeometry}
  | exponentiatedScales => {centeredGeometry, exponentiatedScales}
  | leastSquaresProjection => {leastSquaresProjection}
  | logMeanInvariance => {centeredGeometry, exponentiatedScales, logMeanInvariance}
  | separableModel => {separableModel}
  | rankOneExactness => {leastSquaresProjection, separableModel, rankOneExactness}
  | iteratePreservation => {centeredGeometry, iteratePreservation}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem dependency_branches :
    centeredGeometry ≤ exponentiatedScales ∧
    exponentiatedScales ≤ logMeanInvariance ∧
    leastSquaresProjection ≤ rankOneExactness ∧
    separableModel ≤ rankOneExactness ∧
    centeredGeometry ≤ iteratePreservation := by
  change prerequisites centeredGeometry ⊆ prerequisites exponentiatedScales ∧
    prerequisites exponentiatedScales ⊆ prerequisites logMeanInvariance ∧
    prerequisites leastSquaresProjection ⊆ prerequisites rankOneExactness ∧
    prerequisites separableModel ⊆ prerequisites rankOneExactness ∧
    prerequisites centeredGeometry ⊆ prerequisites iteratePreservation
  decide

theorem reconstruction_and_log_invariance_incomparable :
    ¬ rankOneExactness ≤ logMeanInvariance ∧ ¬ logMeanInvariance ≤ rankOneExactness := by
  change ¬ prerequisites rankOneExactness ⊆ prerequisites logMeanInvariance ∧
    ¬ prerequisites logMeanInvariance ⊆ prerequisites rankOneExactness
  decide

end PipelineDependency

noncomputable section

variable {rowCount acquisitionCount : ℕ}

def acquisitionScales (center : aitchisonSpace acquisitionCount) : Fin acquisitionCount → ℝ :=
  fun acquisition => Real.exp (center.val acquisition)

theorem acquisition_scales_pos (center : aitchisonSpace acquisitionCount)
    (acquisition : Fin acquisitionCount) :
    0 < acquisitionScales center acquisition := Real.exp_pos _

theorem acquisition_scales_product (center : aitchisonSpace acquisitionCount) :
    ∏ acquisition, acquisitionScales center acquisition = 1 :=
  acquisition_scales_product_one center

theorem acquisition_scales_norm_pos (center : aitchisonSpace acquisitionCount)
    (count_pos : 0 < acquisitionCount) :
    0 < scaleSquareSum (acquisitionScales center) :=
  scale_square_sum_pos _ count_pos (acquisition_scales_pos center)

theorem transported_log_sum
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (center : aitchisonSpace acquisitionCount) (row : Fin rowCount)
    (observed_pos : ∀ acquisition, 0 < observed row acquisition) :
    (∑ acquisition, Real.log (multiplicativeTransport observed (acquisitionScales center)
      row acquisition)) = ∑ acquisition, Real.log (observed row acquisition) := by
  have term (acquisition : Fin acquisitionCount) :
      Real.log (multiplicativeTransport observed (acquisitionScales center) row acquisition) =
        Real.log (observed row acquisition) - center.val acquisition := by
    rw [multiplicativeTransport, acquisitionScales,
      Real.log_div (ne_of_gt (observed_pos acquisition)) (Real.exp_ne_zero _), Real.log_exp]
  simp_rw [term]
  rw [Finset.sum_sub_distrib]
  have centered : ∑ acquisition, center.val acquisition = 0 := center.property
  rw [centered, sub_zero]

theorem transported_geometric_mean
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (center : aitchisonSpace acquisitionCount) (row : Fin rowCount)
    (observed_pos : ∀ acquisition, 0 < observed row acquisition) :
    geometricMean (multiplicativeTransport observed (acquisitionScales center) row) =
      geometricMean (observed row) := by
  unfold geometricMean mean
  rw [transported_log_sum observed center row observed_pos]

theorem transported_product
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (center : aitchisonSpace acquisitionCount) (row : Fin rowCount) :
    (∏ acquisition, multiplicativeTransport observed (acquisitionScales center) row acquisition) =
      ∏ acquisition, observed row acquisition := by
  simp only [multiplicativeTransport, Finset.prod_div_distrib,
    acquisition_scales_product, div_one]

theorem recovered_profile_pos
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (center : aitchisonSpace acquisitionCount) (row : Fin rowCount)
    (count_pos : 0 < acquisitionCount)
    (observed_pos : ∀ acquisition, 0 < observed row acquisition) :
    0 < optimalProfile observed (acquisitionScales center) row :=
  optimal_profile_pos observed _ row count_pos observed_pos (acquisition_scales_pos center)

theorem recovered_profile_unique_minimum
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (center : aitchisonSpace acquisitionCount) (row : Fin rowCount) (coefficient : ℝ)
    (count_pos : 0 < acquisitionCount) :
    rowLoss (observed row) (acquisitionScales center) coefficient =
      rowLoss (observed row) (acquisitionScales center)
        (optimalProfile observed (acquisitionScales center) row) ↔
      coefficient = optimalProfile observed (acquisitionScales center) row :=
  row_loss_eq_minimum_iff observed _ row coefficient
    (ne_of_gt (acquisition_scales_norm_pos center count_pos))

theorem separable_centered_pipeline_exact
    (profile : Fin rowCount → ℝ) (center : aitchisonSpace acquisitionCount)
    (count_pos : 0 < acquisitionCount) :
    optimalProfile (responseMatrix profile (acquisitionScales center))
        (acquisitionScales center) = profile ∧
      reconstruction (responseMatrix profile (acquisitionScales center)) (acquisitionScales center) =
        responseMatrix profile (acquisitionScales center) ∧
      multiplicativeTransport (responseMatrix profile (acquisitionScales center))
        (acquisitionScales center) = fun row _ => profile row := by
  have norm_ne := ne_of_gt (acquisition_scales_norm_pos center count_pos)
  exact ⟨optimal_profile_exact profile _ norm_ne, reconstruction_exact profile _ norm_ne,
    response_collapse profile _ (fun acquisition =>
      ne_of_gt (acquisition_scales_pos center acquisition))⟩

theorem normalized_profile_recovery
    (profile : Fin rowCount → ℝ) (scales : Fin acquisitionCount → ℝ)
    (count_pos : 0 < acquisitionCount) (scales_pos : ∀ acquisition, 0 < scales acquisition) :
    optimalProfile (responseMatrix profile scales) (normalizedScales scales) =
      fun row => profile row * geometricMean scales := by
  have normalized_pos : ∀ acquisition, 0 < normalizedScales scales acquisition :=
    fun acquisition => div_pos (scales_pos acquisition) (geometric_mean_pos scales)
  rw [normalized_factorization profile scales]
  exact optimal_profile_exact _ _
    (ne_of_gt (scale_square_sum_pos _ count_pos normalized_pos))

def trajectoryIterate
    (observed : Fin rowCount → aitchisonSpace acquisitionCount)
    (initial : aitchisonSpace acquisitionCount) (cutoff temperature : ℝ) (step : ℕ) :
    EuclideanSpace ℝ (Fin acquisitionCount) :=
  (annealedStep (fun row => (observed row).val) cutoff temperature)^[step] initial.val

theorem trajectory_iterate_mem
    (observed : Fin rowCount → aitchisonSpace acquisitionCount)
    (initial : aitchisonSpace acquisitionCount) (cutoff temperature : ℝ) (step : ℕ) :
    trajectoryIterate observed initial cutoff temperature step ∈ aitchisonSpace acquisitionCount :=
  annealed_iterates_mem_submodule _ _ _ cutoff temperature
    (fun row => (observed row).property) initial.property step

theorem trajectory_limit_mem
    (observed : Fin rowCount → aitchisonSpace acquisitionCount)
    (initial : aitchisonSpace acquisitionCount) (cutoff temperature : ℝ)
    (limit : EuclideanSpace ℝ (Fin acquisitionCount))
    (converges : Tendsto (trajectoryIterate observed initial cutoff temperature) atTop (𝓝 limit)) :
    limit ∈ aitchisonSpace acquisitionCount := by
  apply (aitchisonSpace acquisitionCount).closed_of_finiteDimensional.mem_of_tendsto converges
  exact Filter.Eventually.of_forall (trajectory_iterate_mem observed initial cutoff temperature)

theorem limit_scales_product_one
    (observed : Fin rowCount → aitchisonSpace acquisitionCount)
    (initial : aitchisonSpace acquisitionCount) (cutoff temperature : ℝ)
    (limit : EuclideanSpace ℝ (Fin acquisitionCount))
    (converges : Tendsto (trajectoryIterate observed initial cutoff temperature) atTop (𝓝 limit)) :
    ∏ acquisition, Real.exp (limit acquisition) = 1 :=
  acquisition_scales_product_one
    ⟨limit, trajectory_limit_mem observed initial cutoff temperature limit converges⟩

end

end InfoGeometry.Spectrometry.ThermodynamicTransportPipeline
