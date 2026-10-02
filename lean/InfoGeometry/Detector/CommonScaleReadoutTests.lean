import InfoGeometry.Detector.CommonScaleReadoutDependency

namespace InfoGeometry.Detector.CommonScaleReadout

example (volume distance offset : ℝ) (positive_volume : 0 < volume)
    (nonzero_separation : distance + offset ≠ 0) :
    (volume * (3 / (distance + offset) ^ 2)) /
      Real.sqrt (volume ^ 2 * (4 / (distance + offset) ^ 4)) = 3 / 2 := by
  have root : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1
    norm_num
  simpa only [root] using inverse_square_readout volume 3 4 distance offset positive_volume
    (by norm_num) nonzero_separation

example (scale : ℝ → ℝ) (positive : ∀ time, 0 < scale time) (time : ℝ) :
    HasDerivAt (fun instant => readout 3 4 (scale instant)) 0 time :=
  hasDerivAt_readout_path scale 3 4 (by norm_num) positive time

example : readout 1 1 0 ≠ (1 : ℝ) / Real.sqrt 1 := by
  norm_num [readout_at_zero]

example : readout 1 1 (-1) ≠ readout 1 1 1 := by
  norm_num [readout]

example : readout 3 0 2 = 0 := by
  norm_num [readout]

example (function : ℂ → ℝ) (center : ℂ)
    (harmonic : InnerProductSpace.HarmonicOnNhd function (Metric.closedBall center 2)) :
    Real.circleAverage function center 1 = Real.circleAverage function center 2 := by
  apply InfoGeometry.EmergentGeometry.HarmonicMeanValue.circleAverage_radius_invariant
  · intro point in_ball
    apply harmonic point
    exact Metric.closedBall_subset_closedBall (by norm_num) in_ball
  · simpa using harmonic

example :
    ¬ ProofDependency.Archetype.concentricMeans ≤ ProofDependency.Archetype.constantDerivative ∧
    ¬ ProofDependency.Archetype.constantDerivative ≤ ProofDependency.Archetype.concentricMeans :=
  ProofDependency.harmonic_and_algebraic_branches_incomparable

#print axioms sqrt_quadratic_scale
#print axioms readout_eq
#print axioms readout_invariant
#print axioms inverse_square_readout
#print axioms hasFDerivAt_readout_comp
#print axioms hasDerivAt_readout_path
#print axioms readout_at_zero
#print axioms readout_neg_scale
#print axioms InfoGeometry.EmergentGeometry.HarmonicMeanValue.circleAverage_radius_invariant
#print axioms ProofDependency.dependency_edges
#print axioms ProofDependency.harmonic_and_algebraic_branches_incomparable
#print axioms ProofDependency.model_and_derivative_incomparable

end InfoGeometry.Detector.CommonScaleReadout
