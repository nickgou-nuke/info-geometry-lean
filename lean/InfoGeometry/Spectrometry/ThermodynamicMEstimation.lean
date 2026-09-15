import InfoGeometry.Spectrometry.AitchisonGeometricMedian

namespace InfoGeometry.Spectrometry.ThermodynamicMEstimation

open scoped BigOperators RealInnerProductSpace
open GeometricMedianCore AitchisonGeometricMedian

noncomputable section

variable {Line Space : Type*} [Fintype Line]
variable [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

def gaussianEnergy (observed point : Space) : ℝ :=
  (1 / 2 : ℝ) * ‖point - observed‖ ^ 2

def gaussianObjective (weights : Line → ℝ) (observed : Line → Space)
    (point : Space) : ℝ :=
  ∑ line, weights line * gaussianEnergy (observed line) point

theorem hasFDerivAt_gaussianEnergy (observed point : Space) :
    HasFDerivAt (gaussianEnergy observed) (innerSL ℝ (point - observed)) point := by
  have derivative := ((hasStrictFDerivAt_norm_sq (point - observed)).hasFDerivAt.comp
    point ((hasFDerivAt_id point).sub_const observed)).const_mul (1 / 2 : ℝ)
  convert derivative using 1
  ext direction
  simp [ContinuousLinearMap.smul_apply]

theorem hasFDerivAt_gaussianObjective
    (weights : Line → ℝ) (observed : Line → Space) (point : Space) :
    HasFDerivAt (gaussianObjective weights observed)
      (innerSL ℝ (weightedScore weights observed point)) point := by
  have derivative := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun line _ => (hasFDerivAt_gaussianEnergy (observed line) point).const_mul
      (weights line))
  convert derivative using 1
  ext direction
  simp [weightedScore]

theorem gaussian_stationary_iff_barycenter
    (weights : Line → ℝ) (observed : Line → Space) (point : Space)
    (mass_ne : (∑ line, weights line) ≠ 0) :
    fderiv ℝ (gaussianObjective weights observed) point = 0 ↔
      weightedCenter weights observed = point := by
  rw [(hasFDerivAt_gaussianObjective weights observed point).fderiv]
  have score_iff : innerSL ℝ (weightedScore weights observed point) = 0 ↔
      weightedScore weights observed point = 0 := by
    simpa using (innerSL_inj (𝕜 := ℝ)
      (x := weightedScore weights observed point) (y := (0 : Space)))
  rw [score_iff]
  exact weightedScore_zero_iff_fixed weights observed point mass_ne

theorem laplace_stationary_iff_weiszfeld [Nonempty Line]
    (observed : Line → Space) (point : Space) (regular : RegularAt observed point) :
    fderiv ℝ (distanceObjective observed) point = 0 ↔
      weiszfeldStep observed point = point := by
  rw [(hasFDerivAt_distanceObjective observed point regular).fderiv]
  have score_iff : innerSL ℝ (weightedScore (inverseDistance observed point) observed point) = 0 ↔
      weightedScore (inverseDistance observed point) observed point = 0 := by
    simpa using (innerSL_inj (𝕜 := ℝ)
      (x := weightedScore (inverseDistance observed point) observed point) (y := (0 : Space)))
  rw [score_iff]
  exact weightedScore_zero_iff_fixed _ _ _
    (ne_of_gt (mass_pos _ (inverse_distance_pos observed point regular)))

theorem compound_weight_formula (distance cutoff temperature : ℝ) :
    compoundWeight distance cutoff temperature =
      1 / (distance * (1 + Real.exp ((distance - cutoff) / temperature))) := by
  rw [compoundWeight, DecoupledThermodynamics.line_weight_eq_logistic]
  rw [div_div, mul_comm distance]

theorem annealed_fixed_point_hasFDerivAt_zero [Nonempty Line]
    (observed : Line → Space) (point : Space) (cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) (regular : RegularAt observed point)
    (fixed : annealedStep observed cutoff temperature point = point) :
    HasFDerivAt (annealedObjective observed cutoff temperature) (0 : Space →L[ℝ] ℝ) point := by
  have derivative := hasFDerivAt_annealedObjective observed point cutoff temperature
    temperature_pos regular
  have stationary := (annealed_stationary_iff_fixed observed point cutoff temperature
    temperature_pos regular).mpr fixed
  rw [derivative.fderiv] at stationary
  rwa [stationary] at derivative

end

end InfoGeometry.Spectrometry.ThermodynamicMEstimation
