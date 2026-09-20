import InfoGeometry.Exceptional.CuntzFiniteSynthesis

namespace InfoGeometry.Exceptional.CuntzFiniteSynthesisTests

open CuntzFiniteSynthesis
open InfoGeometry.Canonical.SplitQuaternionMatrixModel

example : cuntzContext ≤ orthogonalityContext := cuntz_precedes_orthogonality

example : ¬ nullContext ≤ orthogonalityContext :=
  algebraic_branches_are_incomparable.2

example : splitQuaternionMatrix 0 1 1 0 ≠ 0 ∧
    Matrix.det (splitQuaternionMatrix 0 1 1 0) = 0 ∧
    splitQuaternionMatrix 0 1 1 0 * splitQuaternionMatrix 0 1 1 0 = 0 :=
  nonzero_null_matrix_family (by norm_num)

example : Matrix.det (splitQuaternionMatrix 0 0 1 1) < 0 :=
  same_sign_state_has_negative_determinant (by norm_num)

example : Matrix.det (splitQuaternionMatrix 0 0 1 1) = -2 := by
  rw [split_matrix_determinant_eq_owner_norm,
    CuntzArchimedeanColimit.equal_negative_coordinates_norm]
  norm_num

example : intervalProjection (-1) = 0 := by
  norm_num [intervalProjection, Set.projIcc]

example : intervalProjection 2 = 1 := by
  norm_num [intervalProjection, Set.projIcc]

example : intervalProjection (1 / 2) = 1 / 2 := by
  apply (interval_projection_fixed_iff _).mpr
  constructor <;> norm_num

example : ∃ point : ℝ, point ≠ 1 / 2 ∧ intervalProjection point = point := by
  refine ⟨0, by norm_num, ?_⟩
  apply (interval_projection_fixed_iff _).mpr
  constructor <;> norm_num

example (point : ℝ) :
    intervalProjection (intervalProjection point) = intervalProjection point :=
  interval_projection_idempotent point

example : (1 / 2 : ℝ) * (1 - 1 / 2) = 1 / 4 :=
  (quadratic_balance_equality_iff (1 / 2)).mpr rfl

example : (0 : ℝ) * (1 - 0) ≠ 1 / 4 := by
  rw [quadratic_balance_equality_iff]
  norm_num

example {Algebra : Type*} [Ring Algebra] [StarRing Algebra]
    (first second operator : Algebra)
    (firstIsometry : star first * first = 1)
    (secondIsometry : star second * second = 1)
    (partition : first * star first + second * star second = 1) :
    operator * (star first * second) = 0 ∧
      (star first * second) * operator = 0 := by
  exact ⟨orthogonality_survives_left_multiplication first second
    firstIsometry secondIsometry partition operator,
    orthogonality_survives_right_multiplication first second
      firstIsometry secondIsometry partition operator⟩

#print axioms cuntz_precedes_orthogonality
#print axioms matrix_precedes_null_family
#print axioms algebraic_branches_are_incomparable
#print axioms projection_is_independent
#print axioms orthogonality_survives_left_multiplication
#print axioms orthogonality_survives_right_multiplication
#print axioms split_matrix_determinant_eq_owner_norm
#print axioms same_sign_state_has_negative_determinant
#print axioms nonzero_null_matrix_family
#print axioms intervalProjection_mem
#print axioms interval_projection_fixed_iff
#print axioms interval_projection_idempotent
#print axioms interval_projection_surjective
#print axioms interval_projection_not_injective
#print axioms quadratic_balance_identity
#print axioms quadratic_balance_upper_bound
#print axioms quadratic_balance_equality_iff

end InfoGeometry.Exceptional.CuntzFiniteSynthesisTests
