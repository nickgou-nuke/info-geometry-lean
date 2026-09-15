import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

namespace InfoGeometry.Spectrometry.GeometricMedianCore

open scoped BigOperators Topology RealInnerProductSpace
open Filter

noncomputable section

variable {Line Space : Type*} [Fintype Line]
variable [NormedAddCommGroup Space]

section NormedGeometry

variable [NormedSpace ℝ Space]

def distanceObjective (observed : Line → Space) (point : Space) : ℝ :=
  ∑ line, ‖point - observed line‖

def IsGeometricMedian (observed : Line → Space) (point : Space) : Prop :=
  ∀ candidate, distanceObjective observed point ≤ distanceObjective observed candidate

def RegularAt (observed : Line → Space) (point : Space) : Prop :=
  ∀ line, point ≠ observed line

def normalizedWeight (weights : Line → ℝ) (line : Line) : ℝ :=
  weights line / ∑ index, weights index

def weightedCenter (weights : Line → ℝ) (observed : Line → Space) : Space :=
  Finset.univ.centerMass weights observed

def weightedScore (weights : Line → ℝ) (observed : Line → Space) (point : Space) : Space :=
  ∑ line, weights line • (point - observed line)

theorem mass_pos [Nonempty Line]
    (weights : Line → ℝ) (weights_pos : ∀ line, 0 < weights line) :
    0 < ∑ line, weights line := by
  exact Finset.sum_pos (fun line _ => weights_pos line) Finset.univ_nonempty

theorem normalized_weights_sum_one [Nonempty Line]
    (weights : Line → ℝ) (weights_pos : ∀ line, 0 < weights line) :
    ∑ line, normalizedWeight weights line = 1 := by
  simp only [normalizedWeight, ← Finset.sum_div]
  exact div_self (ne_of_gt (mass_pos weights weights_pos))

theorem weightedCenter_eq_sum (weights : Line → ℝ) (observed : Line → Space) :
    weightedCenter weights observed =
      ∑ line, normalizedWeight weights line • observed line := by
  simp only [weightedCenter, Finset.centerMass, normalizedWeight,
    Finset.smul_sum, div_eq_mul_inv, mul_smul]
  congr 1
  ext line
  rw [smul_comm]

theorem weightedCenter_mem_submodule
    (subspace : Submodule ℝ Space) (weights : Line → ℝ) (observed : Line → Space)
    (observed_mem : ∀ line, observed line ∈ subspace) :
    weightedCenter weights observed ∈ subspace := by
  exact subspace.smul_mem _
    (subspace.sum_mem (fun line _ => subspace.smul_mem _ (observed_mem line)))

theorem weightedCenter_mem_convexHull [Nonempty Line]
    (weights : Line → ℝ) (observed : Line → Space)
    (weights_pos : ∀ line, 0 < weights line) :
    weightedCenter weights observed ∈ convexHull ℝ (Set.range observed) := by
  exact (convex_convexHull ℝ _).centerMass_mem
    (fun line _ => (weights_pos line).le) (mass_pos weights weights_pos)
    (fun line _ => subset_convexHull ℝ _ (Set.mem_range_self line))

theorem weightedScore_eq
    (weights : Line → ℝ) (observed : Line → Space) (point : Space) :
    weightedScore weights observed point =
      (∑ line, weights line) • point - ∑ line, weights line • observed line := by
  simp [weightedScore, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]

theorem weightedScore_zero_iff_fixed
    (weights : Line → ℝ) (observed : Line → Space) (point : Space)
    (mass_ne : (∑ line, weights line) ≠ 0) :
    weightedScore weights observed point = 0 ↔ weightedCenter weights observed = point := by
  rw [weightedScore_eq, sub_eq_zero]
  constructor
  · intro score_zero
    simp only [weightedCenter, Finset.centerMass, ← score_zero, smul_smul,
      inv_mul_cancel₀ mass_ne, one_smul]
  · intro fixed
    have scaled := congrArg (fun vector => (∑ line, weights line) • vector) fixed
    simpa [weightedCenter, Finset.centerMass, smul_smul, mass_ne] using scaled.symm

omit [NormedSpace ℝ Space] in
theorem continuous_distanceObjective (observed : Line → Space) :
    Continuous (distanceObjective observed) := by
  unfold distanceObjective
  fun_prop

omit [NormedSpace ℝ Space] in
theorem norm_sub_le_distanceObjective
    (observed : Line → Space) (point : Space) (line : Line) :
    ‖point‖ - ‖observed line‖ ≤ distanceObjective observed point := by
  have triangle := norm_sub_norm_le point (observed line)
  exact triangle.trans
    (Finset.single_le_sum (fun index _ => norm_nonneg (point - observed index))
      (Finset.mem_univ line))

omit [NormedSpace ℝ Space] in
theorem exists_geometricMedian [Nonempty Line] [ProperSpace Space]
    (observed : Line → Space) : ∃ point, IsGeometricMedian observed point := by
  obtain ⟨selected⟩ := ‹Nonempty Line›
  apply (continuous_distanceObjective observed).exists_forall_le
  apply Filter.tendsto_atTop_mono (fun point =>
    norm_sub_le_distanceObjective observed point selected)
  apply tendsto_atTop.mpr
  intro bound
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
    (eventually_ge_atTop (bound + ‖observed selected‖))] with point point_bound
  linarith

omit [NormedSpace ℝ Space] in
theorem coincident_is_geometricMedian (point : Space) :
    IsGeometricMedian (fun _ : Line => point) point := by
  intro candidate
  simp only [distanceObjective, sub_self, norm_zero, Finset.sum_const_zero]
  exact Finset.sum_nonneg (fun line _ => norm_nonneg (candidate - point))

theorem distanceObjective_isometry
    (isometry : Space ≃ₗᵢ[ℝ] Space) (observed : Line → Space) (point : Space) :
    distanceObjective (fun line => isometry (observed line)) (isometry point) =
      distanceObjective observed point := by
  simp only [distanceObjective, ← map_sub, isometry.norm_map]

theorem geometricMedian_isometry
    (isometry : Space ≃ₗᵢ[ℝ] Space) (observed : Line → Space) (point : Space)
    (minimal : IsGeometricMedian observed point) :
    IsGeometricMedian (fun line => isometry (observed line)) (isometry point) := by
  intro candidate
  rw [distanceObjective_isometry]
  have transported := distanceObjective_isometry isometry observed (isometry.symm candidate)
  rw [isometry.apply_symm_apply] at transported
  rw [transported]
  exact minimal _

end NormedGeometry

section Derivatives

variable [InnerProductSpace ℝ Space]

theorem hasFDerivAt_euclideanNorm (point : Space) (point_ne : point ≠ 0) :
    HasFDerivAt (fun vector : Space => ‖vector‖)
      (‖point‖⁻¹ • innerSL ℝ point) point := by
  have norm_ne : ‖point‖ ≠ 0 := norm_ne_zero_iff.mpr point_ne
  have derivative :=
    (hasStrictFDerivAt_norm_sq point).hasFDerivAt.sqrt (pow_ne_zero 2 norm_ne)
  convert derivative using 1
  · ext vector
    exact (Real.sqrt_sq (norm_nonneg vector)).symm
  · ext direction
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
      Real.sqrt_sq (norm_nonneg point), nsmul_eq_mul]
    ring

theorem hasFDerivAt_distance (observed point : Space) (distinct : point ≠ observed) :
    HasFDerivAt (fun candidate => ‖candidate - observed‖)
      (‖point - observed‖⁻¹ • innerSL ℝ (point - observed)) point := by
  simpa using (hasFDerivAt_euclideanNorm (point - observed)
    (sub_ne_zero.mpr distinct)).comp point ((hasFDerivAt_id point).sub_const observed)

def inverseDistance (observed : Line → Space) (point : Space) (line : Line) : ℝ :=
  ‖point - observed line‖⁻¹

def weiszfeldStep (observed : Line → Space) (point : Space) : Space :=
  weightedCenter (inverseDistance observed point) observed

omit [Fintype Line] [InnerProductSpace ℝ Space] in
theorem inverse_distance_pos
    (observed : Line → Space) (point : Space) (regular : RegularAt observed point)
    (line : Line) : 0 < inverseDistance observed point line := by
  exact inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr (regular line)))

theorem hasFDerivAt_distanceObjective
    (observed : Line → Space) (point : Space) (regular : RegularAt observed point) :
    HasFDerivAt (distanceObjective observed)
      (innerSL ℝ (weightedScore (inverseDistance observed point) observed point)) point := by
  have derivative := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun line _ => hasFDerivAt_distance (observed line) point (regular line))
  convert derivative using 1
  ext direction
  simp [weightedScore, inverseDistance]

theorem geometricMedian_fixed_point [Nonempty Line]
    (observed : Line → Space) (point : Space)
    (regular : RegularAt observed point) (minimal : IsGeometricMedian observed point) :
    weiszfeldStep observed point = point := by
  have local_min : IsLocalMin (distanceObjective observed) point :=
    Filter.Eventually.of_forall minimal
  have score_zero : weightedScore (inverseDistance observed point) observed point = 0 := by
    have derivative_zero := local_min.fderiv_eq_zero
    rw [(hasFDerivAt_distanceObjective observed point regular).fderiv] at derivative_zero
    have self_inner := congrArg
      (fun functional => functional (weightedScore (inverseDistance observed point) observed point))
      derivative_zero
    simpa using self_inner
  exact (weightedScore_zero_iff_fixed _ _ _
    (ne_of_gt (mass_pos _ (inverse_distance_pos observed point regular)))).mp score_zero

end Derivatives

end

end InfoGeometry.Spectrometry.GeometricMedianCore
