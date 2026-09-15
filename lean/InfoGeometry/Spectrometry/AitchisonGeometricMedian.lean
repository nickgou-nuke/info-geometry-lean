import InfoGeometry.Spectrometry.GeometricMedianCore
import InfoGeometry.Spectrometry.DecoupledThermodynamics
import Mathlib.Analysis.InnerProductSpace.Dual

namespace InfoGeometry.Spectrometry.AitchisonGeometricMedian

open scoped BigOperators Topology RealInnerProductSpace
open Filter

namespace ProofDependency

inductive Archetype
  | centeredGeometry
  | inverseDistance
  | thermalWeights
  | subspacePreservation
  | outlierDamping
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | centeredGeometry => {centeredGeometry}
  | inverseDistance => {inverseDistance}
  | thermalWeights => {inverseDistance, thermalWeights}
  | subspacePreservation =>
      {centeredGeometry, inverseDistance, thermalWeights, subspacePreservation}
  | outlierDamping => {inverseDistance, thermalWeights, outlierDamping}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem preservation_and_damping_incomparable :
    ¬ subspacePreservation ≤ outlierDamping ∧
      ¬ outlierDamping ≤ subspacePreservation := by
  change ¬ prerequisites subspacePreservation ⊆ prerequisites outlierDamping ∧
    ¬ prerequisites outlierDamping ⊆ prerequisites subspacePreservation
  decide

end ProofDependency

open GeometricMedianCore DecoupledThermodynamics

noncomputable section

def aitchisonSpace (acquisitionCount : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin acquisitionCount)) :=
  (zeroSumSpace acquisitionCount).comap (EuclideanSpace.equiv (Fin acquisitionCount) ℝ).toLinearMap

def clrTrajectory {acquisitionCount : ℕ}
    (values : Fin acquisitionCount → ℝ) (count_pos : 0 < acquisitionCount) :
    aitchisonSpace acquisitionCount :=
  ⟨WithLp.toLp 2 (RobustThermodynamics.clr values),
    RobustThermodynamics.clr_sum_zero values count_pos⟩

theorem clr_trajectory_scale_invariant {acquisitionCount : ℕ}
    (values : Fin acquisitionCount → ℝ) (amplitude : ℝ)
    (count_pos : 0 < acquisitionCount) (amplitude_pos : 0 < amplitude)
    (values_pos : ∀ acquisition, 0 < values acquisition) :
    clrTrajectory (fun acquisition => amplitude * values acquisition) count_pos =
      clrTrajectory values count_pos := by
  apply Subtype.ext
  change WithLp.toLp 2 (RobustThermodynamics.clr
    (fun acquisition => amplitude * values acquisition)) =
      WithLp.toLp 2 (RobustThermodynamics.clr values)
  rw [RobustThermodynamics.clr_scale_invariant values amplitude
    count_pos amplitude_pos values_pos]

theorem acquisition_scales_product_one {acquisitionCount : ℕ}
    (point : aitchisonSpace acquisitionCount) :
    ∏ acquisition, Real.exp (point.val acquisition) = 1 := by
  rw [← Real.exp_sum]
  have centered : ∑ acquisition, point.val acquisition = 0 := point.property
  rw [centered, Real.exp_zero]

theorem exists_aitchison_geometricMedian
    {Line : Type*} [Fintype Line] [Nonempty Line] {acquisitionCount : ℕ}
    (observed : Line → aitchisonSpace acquisitionCount) :
    ∃ point, IsGeometricMedian observed point := by
  exact exists_geometricMedian observed

def compoundWeight (distance cutoff temperature : ℝ) : ℝ :=
  lineWeight distance cutoff temperature / distance

theorem compound_weight_pos (distance cutoff temperature : ℝ) (distance_pos : 0 < distance) :
    0 < compoundWeight distance cutoff temperature := by
  exact div_pos (line_weight_bounds distance cutoff temperature).1 distance_pos

theorem compound_weight_outlier_bound
    (distance cutoff temperature : ℝ) (distance_pos : 0 < distance)
    (temperature_pos : 0 < temperature) (beyond_cutoff : cutoff < distance) :
    compoundWeight distance cutoff temperature < 1 / (2 * distance) := by
  have weight_bound := (line_weight_lt_half_iff distance cutoff temperature temperature_pos).mpr
    beyond_cutoff
  have bound := div_lt_div_of_pos_right weight_bound distance_pos
  simpa only [compoundWeight, div_div] using bound

theorem compound_weight_exponential_bound
    (distance cutoff temperature : ℝ) (distance_pos : 0 < distance) :
    compoundWeight distance cutoff temperature ≤
      Real.exp ((cutoff - distance) / temperature) / distance := by
  exact div_le_div_of_nonneg_right (line_weight_le_exp_gap distance cutoff temperature)
    distance_pos.le

theorem tendsto_compound_weight_atTop
    (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    Tendsto (fun distance => compoundWeight distance cutoff temperature) atTop (𝓝 0) := by
  simpa [compoundWeight, div_eq_mul_inv] using
    (tendsto_line_weight_atTop cutoff temperature temperature_pos).mul tendsto_inv_atTop_zero

section Iteration

variable {Line Space : Type*} [Fintype Line]
variable [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def thermalWeights (observed : Line → Space) (point : Space)
    (cutoff temperature : ℝ) (line : Line) : ℝ :=
  compoundWeight (‖point - observed line‖) cutoff temperature

def annealedStep (observed : Line → Space) (cutoff temperature : ℝ) (point : Space) : Space :=
  weightedCenter (thermalWeights observed point cutoff temperature) observed

def annealedObjective (observed : Line → Space) (cutoff temperature : ℝ) (point : Space) : ℝ :=
  totalFreeEnergy (fun line => ‖point - observed line‖) cutoff temperature

omit [Fintype Line] [NormedSpace ℝ Space] in
theorem thermal_weights_pos
    (observed : Line → Space) (point : Space) (cutoff temperature : ℝ)
    (regular : RegularAt observed point) (line : Line) :
    0 < thermalWeights observed point cutoff temperature line := by
  exact compound_weight_pos _ _ _ (norm_pos_iff.mpr (sub_ne_zero.mpr (regular line)))

omit [NormedSpace ℝ Space] in
theorem thermal_normalized_weights_sum_one [Nonempty Line]
    (observed : Line → Space) (point : Space) (cutoff temperature : ℝ)
    (regular : RegularAt observed point) :
    ∑ line, normalizedWeight (thermalWeights observed point cutoff temperature) line = 1 := by
  exact normalized_weights_sum_one _ (thermal_weights_pos observed point cutoff temperature regular)

theorem annealedStep_mem_convexHull [Nonempty Line]
    (observed : Line → Space) (point : Space) (cutoff temperature : ℝ)
    (regular : RegularAt observed point) :
    annealedStep observed cutoff temperature point ∈ convexHull ℝ (Set.range observed) := by
  exact weightedCenter_mem_convexHull _ _
    (thermal_weights_pos observed point cutoff temperature regular)

theorem annealedStep_mem_submodule
    (subspace : Submodule ℝ Space) (observed : Line → Space) (point : Space)
    (cutoff temperature : ℝ) (observed_mem : ∀ line, observed line ∈ subspace) :
    annealedStep observed cutoff temperature point ∈ subspace := by
  exact weightedCenter_mem_submodule subspace _ observed observed_mem

theorem annealed_iterates_mem_submodule
    (subspace : Submodule ℝ Space) (observed : Line → Space) (initial : Space)
    (cutoff temperature : ℝ) (observed_mem : ∀ line, observed line ∈ subspace)
    (initial_mem : initial ∈ subspace) (iteration : ℕ) :
    (annealedStep observed cutoff temperature)^[iteration] initial ∈ subspace := by
  induction iteration with
  | zero => exact initial_mem
  | succ iteration induction_hypothesis =>
      rw [Function.iterate_succ_apply']
      exact annealedStep_mem_submodule subspace observed _ cutoff temperature observed_mem

theorem annealedStep_isometry
    (isometry : Space ≃ₗᵢ[ℝ] Space) (observed : Line → Space) (point : Space)
    (cutoff temperature : ℝ) :
    annealedStep (fun line => isometry (observed line)) cutoff temperature (isometry point) =
      isometry (annealedStep observed cutoff temperature point) := by
  simp [annealedStep, thermalWeights, weightedCenter, Finset.centerMass, ← map_sub]

theorem single_score_norm
    (observed point : Space) (cutoff temperature : ℝ) (distinct : point ≠ observed) :
    ‖compoundWeight (‖point - observed‖) cutoff temperature • (point - observed)‖ =
      lineWeight (‖point - observed‖) cutoff temperature := by
  have distance_pos := norm_pos_iff.mpr (sub_ne_zero.mpr distinct)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (compound_weight_pos _ cutoff temperature distance_pos)]
  exact div_mul_cancel₀ _ (ne_of_gt distance_pos)

end Iteration

section Stationarity

variable {Line Space : Type*} [Fintype Line]
variable [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

theorem hasFDerivAt_annealedObjective
    (observed : Line → Space) (point : Space) (cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) (regular : RegularAt observed point) :
    HasFDerivAt (annealedObjective observed cutoff temperature)
      (innerSL ℝ (weightedScore (thermalWeights observed point cutoff temperature) observed point))
      point := by
  have derivative := hasFDerivAt_totalFreeEnergy
    (fun line candidate => ‖candidate - observed line‖)
    (fun line => ‖point - observed line‖⁻¹ • innerSL ℝ (point - observed line))
    point cutoff temperature temperature_pos
    (fun line => hasFDerivAt_distance (observed line) point (regular line))
  convert derivative using 1
  ext direction
  simp [weightedScore, thermalWeights, compoundWeight, div_eq_mul_inv, mul_assoc]

theorem annealed_stationary_iff_fixed [Nonempty Line]
    (observed : Line → Space) (point : Space) (cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) (regular : RegularAt observed point) :
    fderiv ℝ (annealedObjective observed cutoff temperature) point = 0 ↔
      annealedStep observed cutoff temperature point = point := by
  rw [(hasFDerivAt_annealedObjective observed point cutoff temperature temperature_pos regular).fderiv]
  have score_iff :
      innerSL ℝ (weightedScore (thermalWeights observed point cutoff temperature) observed point) = 0 ↔
      weightedScore (thermalWeights observed point cutoff temperature) observed point = 0 := by
    simpa using (innerSL_inj (𝕜 := ℝ)
      (x := weightedScore (thermalWeights observed point cutoff temperature) observed point)
      (y := (0 : Space)))
  rw [score_iff]
  exact weightedScore_zero_iff_fixed _ _ _
    (ne_of_gt (mass_pos _ (thermal_weights_pos observed point cutoff temperature regular)))

end Stationarity

end

end InfoGeometry.Spectrometry.AitchisonGeometricMedian
