import InfoGeometry.ScalarStatisticalIdentities
import InfoGeometry.ScalarStatisticalIdentitiesDependencies

namespace InfoGeometry.ScalarStatisticalIdentities

example : odds (1 / 2) = 1 := by norm_num [odds]

example : probabilityFromOdds 3 = 3 / 4 := by norm_num [probabilityFromOdds]

example : probabilityFromOdds (odds 1) ≠ (1 : ℝ) := by
  norm_num [probabilityFromOdds, odds]

example : odds (probabilityFromOdds (-1)) ≠ (-1 : ℝ) := by
  norm_num [probabilityFromOdds, odds]

example : squareRootOdds 3 (probabilityFromOdds 4) = 6 := by
  rw [squareRootOdds, odds_probabilityFromOdds 4 (by norm_num)]
  norm_num

example (calibration probability : ℝ) (nonnegative : 0 ≤ odds probability) :
    squareRootOdds calibration (probabilityFromOdds (0 ^ 2 * odds probability)) =
      0 * squareRootOdds calibration probability :=
  squareRootOdds_scaling calibration probability 0 (by norm_num) nonnegative

example (information variance : ℝ) (inverse_relation : variance * information = 1) :
    (variance / 5) * (5 * information) = 1 :=
  inverse_information_scaling information variance 5 inverse_relation (by norm_num)

example : ((1 : ℝ) / 0) * (0 * 1) ≠ 1 := by norm_num

example : (0 : ℝ) / 0 ≠ 1 := by norm_num

example : Real.sqrt (9 : ℝ) / 9 = 1 / Real.sqrt 9 :=
  equal_moments_relative_fluctuation 9 9 rfl

example : rootScale 2 16 = 1 / 2 := by norm_num [rootScale]

example : rootScale 2 0 = 0 := by norm_num [rootScale]

example (estimate center : ℝ) (bounded : WithinRadius estimate center 0) :
    estimate = center := (zero_radius_iff estimate center).mp bounded

example : standardizedCoordinate 4 0 4 = 2 := by norm_num [standardizedCoordinate]

example : standardizedCoordinate 4 0 16 = standardizedCoordinate 1 0 1 := by
  norm_num [standardizedCoordinate]

example : standardizedCoordinate 4 0 0 = 0 := by simp [standardizedCoordinate]

example : exponentialSeparation 2 (-1) 1 < exponentialSeparation 2 (-1) 0 := by
  unfold exponentialSeparation
  apply mul_lt_mul_of_pos_left _ (by norm_num)
  apply Real.exp_lt_exp.mpr
  norm_num

example : ¬ Archetype.exponentialModel ≤ Archetype.relativeFluctuation := by decide

#print axioms exponentialSeparation_strictMono
#print axioms probabilityFromOdds_odds
#print axioms odds_probabilityFromOdds
#print axioms squareRootOdds_scaling
#print axioms inverse_information_scaling
#print axioms equal_moments_fano_ratio
#print axioms equal_moments_relative_fluctuation
#print axioms rootScale_mul
#print axioms rootScale_antitoneOn
#print axioms zero_radius_iff
#print axioms simultaneous_linear_scaling
#print axioms deterministic_positive_scaling_invariant
#print axioms simultaneous_linear_scaling_not_invariant
#print axioms dependency_branches
#print axioms no_dependency_cycle

end InfoGeometry.ScalarStatisticalIdentities
