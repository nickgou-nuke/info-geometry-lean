import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordTwoModeCAR

/-!
# Concrete nuclear five-grading in the two-mode CAR matrix algebra

The generic Freudenthal bracket candidate has a separately identified mixed
Jacobi obstruction. This file closes the nuclear five-grade lane on a concrete
carrier instead of assuming that obstruction away.

The associative algebra `M₄(ℝ)` carries the two-mode Jordan--Wigner CAR
representation. Its commutator is an ordinary Lie bracket. The centered total
occupation operator defines an adjoint grading with weights `-2,-1,0,1,2`:

* pair annihilation/creation have grades `-2/+2`;
* single annihilation/creation maps have grades `-1/+1`;
* their mixed commutators have grade `0`.

Jacobi is inherited from associative matrix multiplication and is proved for
all matrices, not stored as a field or assumed cellwise.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel

open Matrix
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR

abbrev M4R := InfoGeometry.Algebra.FiniteSpin.Mat4R

/-- Associative matrix commutator. -/
def comm (X Y : M4R) : M4R :=
  X * Y - Y * X

/-- Global Jacobi identity on the concrete operator carrier. -/
theorem comm_jacobi (X Y Z : M4R) :
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 := by
  simp only [comm]
  noncomm_ring

/-- Adjoint derivation law. -/
theorem comm_derivation (H X Y : M4R) :
    comm H (comm X Y) = comm (comm H X) Y + comm X (comm H Y) := by
  simp only [comm]
  noncomm_ring

/-- Occupation of the first CAR mode. -/
def number1 : M4R := a1Dag * a1

/-- Occupation of the second CAR mode. -/
def number2 : M4R := a2Dag * a2

/-- Centered total occupation, with spectrum `-1,0,0,1`. -/
def gradingOperator : M4R :=
  number1 + number2 - 1

/-- Pair creation and annihilation extremes. -/
def pairCreation : M4R := a1Dag * a2Dag

def pairAnnihilation : M4R := a2 * a1

/-- Explicit grading matrix. -/
theorem gradingOperator_eq_diagonal :
    gradingOperator =
      !![-1, 0, 0, 0;
          0, 0, 0, 0;
          0, 0, 0, 0;
          0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gradingOperator, number1, number2, a1, a1Dag, a2, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Adjoint eigenspace predicate for the integer grading. -/
def HasGrade (k : ℤ) (X : M4R) : Prop :=
  comm gradingOperator X = (k : ℝ) • X

/-- Scalar compatibility of the commutator. -/
theorem comm_smul_left (c : ℝ) (X Y : M4R) :
    comm (c • X) Y = c • comm X Y := by
  simp [comm, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- Scalar compatibility of the commutator. -/
theorem comm_smul_right (c : ℝ) (X Y : M4R) :
    comm X (c • Y) = c • comm X Y := by
  simp [comm, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- Brackets add grades. -/
theorem comm_hasGrade
    {k l : ℤ} {X Y : M4R}
    (hX : HasGrade k X) (hY : HasGrade l Y) :
    HasGrade (k + l) (comm X Y) := by
  unfold HasGrade at hX hY ⊢
  rw [comm_derivation, hX, hY,
    comm_smul_left, comm_smul_right, ← add_smul]
  simp only [Int.cast_add]

/-- Grade `+1` creation operators. -/
theorem a1Dag_grade : HasGrade 1 a1Dag := by
  unfold HasGrade
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, a1Dag, Matrix.mul_apply, Fin.sum_univ_four]

theorem a2Dag_grade : HasGrade 1 a2Dag := by
  unfold HasGrade
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- Grade `-1` annihilation operators. -/
theorem a1_grade : HasGrade (-1) a1 := by
  unfold HasGrade
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, a1, Matrix.mul_apply, Fin.sum_univ_four]

theorem a2_grade : HasGrade (-1) a2 := by
  unfold HasGrade
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, a2, Matrix.mul_apply, Fin.sum_univ_four]

/-- Extreme pair operators have grades `±2`. -/
theorem pairCreation_grade : HasGrade 2 pairCreation := by
  unfold HasGrade
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, pairCreation, a1Dag, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem pairAnnihilation_grade : HasGrade (-2) pairAnnihilation := by
  unfold HasGrade
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, pairAnnihilation, a1, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- The extreme operators and the grading operator form an `sl₂` triple. -/
theorem pair_extreme_bracket :
    comm pairCreation pairAnnihilation = gradingOperator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, pairCreation, pairAnnihilation, gradingOperator,
      number1, number2, a1, a1Dag, a2, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem grading_pairCreation :
    comm gradingOperator pairCreation = (2 : ℝ) • pairCreation :=
  pairCreation_grade

theorem grading_pairAnnihilation :
    comm gradingOperator pairAnnihilation = (-2 : ℝ) • pairAnnihilation :=
  by simpa [HasGrade] using pairAnnihilation_grade

/-- Same-sign odd brackets generate the extreme pair lanes. -/
theorem creation_bracket_generates_pair :
    comm a1Dag a2Dag = (2 : ℝ) • pairCreation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, pairCreation, a1Dag, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem annihilation_bracket_generates_pair :
    comm a1 a2 = (-2 : ℝ) • pairAnnihilation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, pairAnnihilation, a1, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Extreme action closes on the adjacent odd lanes. -/
theorem pairCreation_comm_a1 :
    comm pairCreation a1 = -a2Dag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, pairCreation, a1, a1Dag, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem pairCreation_comm_a2 :
    comm pairCreation a2 = a1Dag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, pairCreation, a2, a1Dag, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem pairAnnihilation_comm_a1Dag :
    comm pairAnnihilation a1Dag = a2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, pairAnnihilation, a1Dag, a1, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem pairAnnihilation_comm_a2Dag :
    comm pairAnnihilation a2Dag = -a1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, pairAnnihilation, a2Dag, a1, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Mixed odd brackets lie in the zero-grade eigenspace by the general grade
addition theorem. -/
theorem mixed_a1_a1Dag_grade_zero :
    HasGrade 0 (comm a1 a1Dag) := by
  simpa using comm_hasGrade a1_grade a1Dag_grade

theorem mixed_a1_a2Dag_grade_zero :
    HasGrade 0 (comm a1 a2Dag) := by
  simpa using comm_hasGrade a1_grade a2Dag_grade

theorem mixed_a2_a1Dag_grade_zero :
    HasGrade 0 (comm a2 a1Dag) := by
  simpa using comm_hasGrade a2_grade a1Dag_grade

theorem mixed_a2_a2Dag_grade_zero :
    HasGrade 0 (comm a2 a2Dag) := by
  simpa using comm_hasGrade a2_grade a2Dag_grade

/-- The concrete five-grade relation packet has global Jacobi because it lives
inside an associative matrix algebra. -/
theorem concrete_nuclear_five_grade_packet (X Y Z : M4R) :
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 ∧
      HasGrade 2 pairCreation ∧
      HasGrade 1 a1Dag ∧
      HasGrade 1 a2Dag ∧
      HasGrade 0 (comm a1 a1Dag) ∧
      HasGrade (-1) a1 ∧
      HasGrade (-1) a2 ∧
      HasGrade (-2) pairAnnihilation ∧
      comm pairCreation pairAnnihilation = gradingOperator := by
  exact ⟨comm_jacobi X Y Z,
    pairCreation_grade, a1Dag_grade, a2Dag_grade,
    mixed_a1_a1Dag_grade_zero,
    a1_grade, a2_grade, pairAnnihilation_grade,
    pair_extreme_bracket⟩

end InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
