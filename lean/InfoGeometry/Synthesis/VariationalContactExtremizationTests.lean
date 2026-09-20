import InfoGeometry.Synthesis.VariationalContactExtremization

namespace InfoGeometry.Synthesis.VariationalContactExtremizationTests

open VariationalContactExtremization QuadraticContactDerivatives ImpedanceMatchingDuality

example (coupling : ℝ) (point : ℝ × ℝ) :
    HasFDerivAt (contactAction coupling) (contactDifferential coupling point) point :=
  contactAction_hasFDerivAt coupling point

example : contactDifferential 1 (1 / 2, 0) = 0 := by
  apply (contactDifferential_eq_zero_iff 1 _ (by norm_num)).mpr
  norm_num

example : contactAction 1 (1 / 2, 0) < contactAction 1 (0, 0) := by
  simpa using contactAction_strict_global_minimum 1 (by norm_num) (0, 0) (by norm_num)

example : 0 < action 0 0 0 := by
  unfold action
  rw [pointwise_gap]
  norm_num

example (efficiency : ℝ) :
    deriv (deriv (fisher_capacity 1)) efficiency < 0 := by
  rw [capacity_second_deriv]
  norm_num

example (momentum : ℝ) : 0 < deriv (deriv criticalValue) momentum := by
  rw [criticalValue_second_deriv]
  norm_num

#print axioms contactAction_hasFDerivAt
#print axioms contactDifferential_eq_zero_iff
#print axioms contactAction_strict_global_minimum
#print axioms action_second_variation_positive

end InfoGeometry.Synthesis.VariationalContactExtremizationTests
