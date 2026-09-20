import Mathlib
import InfoGeometry.Exceptional.CuntzArchimedeanColimit
import InfoGeometry.Canonical.SplitQuaternionMatrixModel
import InfoGeometry.Probability.SimplexQuadraticResponse

namespace InfoGeometry.Exceptional.CuntzFiniteSynthesis

open InfoGeometry.Canonical.SplitQuaternionMatrixModel
open InfoGeometry.Exceptional.CuntzArchimedeanColimit

inductive Archetype
  | cuntzRelations
  | branchOrthogonality
  | splitMatrixAlgebra
  | determinantFormula
  | nullFamily
  | intervalProjection
  deriving DecidableEq, Fintype

abbrev DependencyContext := Finset Archetype

def cuntzContext : DependencyContext := {.cuntzRelations}

def orthogonalityContext : DependencyContext :=
  cuntzContext ∪ {.branchOrthogonality}

def matrixContext : DependencyContext :=
  {.splitMatrixAlgebra, .determinantFormula}

def nullContext : DependencyContext := matrixContext ∪ {.nullFamily}

def projectionContext : DependencyContext := {.intervalProjection}

theorem cuntz_precedes_orthogonality :
    cuntzContext ≤ orthogonalityContext := by decide

theorem matrix_precedes_null_family :
    matrixContext ≤ nullContext := by decide

theorem algebraic_branches_are_incomparable :
    ¬ orthogonalityContext ≤ nullContext ∧
      ¬ nullContext ≤ orthogonalityContext := by decide

theorem projection_is_independent :
    ¬ projectionContext ≤ nullContext ∧
      ¬ nullContext ≤ projectionContext := by decide

section CuntzRelations

variable {Algebra : Type*} [Ring Algebra] [StarRing Algebra]
variable (first second : Algebra)
variable (firstIsometry : star first * first = 1)
variable (secondIsometry : star second * second = 1)
variable (partition : first * star first + second * star second = 1)

theorem orthogonality_survives_left_multiplication (operator : Algebra) :
    operator * (star first * second) = 0 := by
  rw [(cuntz_branches_orthogonal first second
    firstIsometry secondIsometry partition).1, mul_zero]

theorem orthogonality_survives_right_multiplication (operator : Algebra) :
    (star first * second) * operator = 0 := by
  rw [(cuntz_branches_orthogonal first second
    firstIsometry secondIsometry partition).1, zero_mul]

end CuntzRelations

theorem split_matrix_determinant_eq_owner_norm
    (scalar imaginary firstSplit secondSplit : ℝ) :
    Matrix.det (splitQuaternionMatrix scalar imaginary firstSplit secondSplit) =
      InfoGeometry.Clifford.norm
        (⟨scalar, imaginary, firstSplit, secondSplit⟩ :
          InfoGeometry.Clifford.SplitQuaternion) := by
  rw [splitQuaternionMatrix_det]
  simp only [InfoGeometry.Clifford.norm]
  ring

theorem same_sign_state_has_negative_determinant
    {parameter : ℝ} (nonzero : parameter ≠ 0) :
    Matrix.det (splitQuaternionMatrix 0 0 parameter parameter) < 0 := by
  rw [split_matrix_determinant_eq_owner_norm, equal_negative_coordinates_norm]
  have positiveSquare : 0 < parameter ^ 2 := sq_pos_of_ne_zero nonzero
  nlinarith

theorem nonzero_null_matrix_family
    {parameter : ℝ} (nonzero : parameter ≠ 0) :
    splitQuaternionMatrix 0 parameter parameter 0 ≠ 0 ∧
      Matrix.det (splitQuaternionMatrix 0 parameter parameter 0) = 0 ∧
      splitQuaternionMatrix 0 parameter parameter 0 *
        splitQuaternionMatrix 0 parameter parameter 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro matrixZero
    have entryZero := congrArg (fun matrix : Mat2 => matrix 0 1) matrixZero
    rw [splitQuaternionMatrix_eq] at entryZero
    have twiceZero : parameter + parameter = 0 := by simpa using entryZero
    apply nonzero
    linarith
  · rw [split_matrix_determinant_eq_owner_norm]
    exact opposite_signature_coordinates_null parameter
  · simp only [splitQuaternionMatrix_eq]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

noncomputable section

def intervalProjection (point : ℝ) : ℝ :=
  (Set.projIcc (0 : ℝ) 1 (by norm_num) point : ℝ)

theorem intervalProjection_mem (point : ℝ) :
    intervalProjection point ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 (by norm_num) point).property

theorem interval_projection_fixed_iff (point : ℝ) :
    intervalProjection point = point ↔ point ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · intro fixed
    have member := intervalProjection_mem point
    rwa [fixed] at member
  · intro member
    unfold intervalProjection
    rw [Set.projIcc_of_mem _ member]

theorem interval_projection_idempotent (point : ℝ) :
    intervalProjection (intervalProjection point) = intervalProjection point :=
  (interval_projection_fixed_iff _).mpr (intervalProjection_mem point)

theorem interval_projection_surjective :
    ∀ target ∈ Set.Icc (0 : ℝ) 1,
      ∃ source : ℝ, intervalProjection source = target := by
  intro target member
  exact ⟨target, (interval_projection_fixed_iff target).mpr member⟩

theorem interval_projection_not_injective :
    ¬ Function.Injective intervalProjection := by
  intro injective
  have equalImages : intervalProjection (-1) = intervalProjection 0 := by
    norm_num [intervalProjection, Set.projIcc]
  have impossible : (-1 : ℝ) = 0 := injective equalImages
  norm_num at impossible

theorem quadratic_balance_identity (point : ℝ) :
    point * (1 - point) = 1 / 4 - (point - 1 / 2) ^ 2 := by
  have gap := InfoGeometry.Probability.SimplexQuadraticResponse.vertex_gap
    1 1 point (by norm_num)
  norm_num [InfoGeometry.Probability.SimplexQuadraticResponse.response] at gap
  nlinarith

theorem quadratic_balance_upper_bound (point : ℝ) :
    point * (1 - point) ≤ 1 / 4 :=
  InfoGeometry.Probability.SimplexQuadraticResponse.binary_variance_peak point

theorem quadratic_balance_equality_iff (point : ℝ) :
    point * (1 - point) = 1 / 4 ↔ point = 1 / 2 := by
  rw [quadratic_balance_identity]
  constructor
  · intro equality
    have squareZero : (point - 1 / 2) ^ 2 = 0 := by linarith
    exact (centered_square_zero_iff point).mp squareZero
  · rintro rfl
    norm_num

end

end InfoGeometry.Exceptional.CuntzFiniteSynthesis
