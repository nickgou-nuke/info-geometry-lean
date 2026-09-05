import Mathlib
import InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom

/-!
# Degree-zero `sl₂` inside the concrete nuclear five-grading

The two CAR modes carry an internal number-preserving `sl₂` action.  Its
raising and lowering currents exchange the two one-particle modes, while the
Cartan element is their occupation difference.  All three operators belong to
the zero lane of the total-occupation five-grading.

This is a mathematical degree-zero symmetry and selection-rule packet.  A
physical interpretation as spin, isospin, or another doublet action requires
a separately supplied identification of the two modes.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2

open Matrix
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom

/-- Number-preserving raising current from mode two to mode one. -/
def degreeZeroRaise : M4R :=
  a1Dag * a2

/-- Number-preserving lowering current from mode one to mode two. -/
def degreeZeroLower : M4R :=
  a2Dag * a1

/-- Occupation-difference Cartan element. -/
def degreeZeroCartan : M4R :=
  number1 - number2

/-- The degree-zero triple is explicitly contained in the zero lane. -/
theorem degreeZeroRaise_grade : HasGrade 0 degreeZeroRaise := by
  unfold HasGrade
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroRaise, a1, a1Dag, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeZeroLower_grade : HasGrade 0 degreeZeroLower := by
  unfold HasGrade
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroLower, a1, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeZeroCartan_grade : HasGrade 0 degreeZeroCartan := by
  unfold HasGrade
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroCartan, number1, number2,
      a1, a1Dag, a2, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- Exact `sl₂` bracket relations. -/
theorem degreeZeroCartan_comm_raise :
    comm degreeZeroCartan degreeZeroRaise =
      (2 : ℝ) • degreeZeroRaise := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroCartan, degreeZeroRaise,
      number1, number2, a1, a1Dag, a2, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeZeroCartan_comm_lower :
    comm degreeZeroCartan degreeZeroLower =
      (-2 : ℝ) • degreeZeroLower := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroCartan, degreeZeroLower,
      number1, number2, a1, a1Dag, a2, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeZero_raise_comm_lower :
    comm degreeZeroRaise degreeZeroLower = degreeZeroCartan := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroCartan, degreeZeroRaise, degreeZeroLower,
      number1, number2, a1, a1Dag, a2, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Cartan weights of the one-particle creation doublet. -/
theorem degreeZeroCartan_comm_a1Dag :
    comm degreeZeroCartan a1Dag = a1Dag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroCartan, number1, number2,
      a1, a1Dag, a2, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeZeroCartan_comm_a2Dag :
    comm degreeZeroCartan a2Dag = -a2Dag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroCartan, number1, number2,
      a1, a1Dag, a2, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- Raising/lowering selection rules on the creation doublet. -/
theorem degreeZeroRaise_comm_a2Dag :
    comm degreeZeroRaise a2Dag = a1Dag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroRaise, a1, a1Dag, a2, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeZeroRaise_comm_a1Dag :
    comm degreeZeroRaise a1Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroRaise, a1Dag, a2,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeZeroLower_comm_a1Dag :
    comm degreeZeroLower a1Dag = a2Dag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroLower, a1, a1Dag, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeZeroLower_comm_a2Dag :
    comm degreeZeroLower a2Dag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comm, degreeZeroLower, a1, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- The common-carrier Lie representation preserves this degree-zero `sl₂`
triple and its brackets. -/
theorem represented_degreeZero_sl2_packet :
    RepresentedHasGrade 0 (representation degreeZeroRaise) ∧
      RepresentedHasGrade 0 (representation degreeZeroLower) ∧
      RepresentedHasGrade 0 (representation degreeZeroCartan) ∧
      ⁅commonRepresentationLieHom degreeZeroCartan,
          commonRepresentationLieHom degreeZeroRaise⁆ =
        (2 : ℝ) • commonRepresentationLieHom degreeZeroRaise ∧
      ⁅commonRepresentationLieHom degreeZeroRaise,
          commonRepresentationLieHom degreeZeroLower⁆ =
        commonRepresentationLieHom degreeZeroCartan := by
  refine ⟨representation_preserves_grade degreeZeroRaise_grade,
    representation_preserves_grade degreeZeroLower_grade,
    representation_preserves_grade degreeZeroCartan_grade, ?_, ?_⟩
  · rw [← commonRepresentationLieHom.map_lie,
      degreeZeroCartan_comm_raise]
    exact commonRepresentationLieHom.map_smul _ _
  · rw [← commonRepresentationLieHom.map_lie,
      degreeZero_raise_comm_lower]

/-- Complete degree-zero symmetry and selection-rule packet. -/
theorem degree_zero_sl2_selection_packet :
    HasGrade 0 degreeZeroRaise ∧
      HasGrade 0 degreeZeroLower ∧
      HasGrade 0 degreeZeroCartan ∧
      comm degreeZeroCartan degreeZeroRaise =
        (2 : ℝ) • degreeZeroRaise ∧
      comm degreeZeroCartan degreeZeroLower =
        (-2 : ℝ) • degreeZeroLower ∧
      comm degreeZeroRaise degreeZeroLower = degreeZeroCartan ∧
      comm degreeZeroCartan a1Dag = a1Dag ∧
      comm degreeZeroCartan a2Dag = -a2Dag ∧
      comm degreeZeroRaise a2Dag = a1Dag ∧
      comm degreeZeroLower a1Dag = a2Dag := by
  exact ⟨degreeZeroRaise_grade, degreeZeroLower_grade,
    degreeZeroCartan_grade, degreeZeroCartan_comm_raise,
    degreeZeroCartan_comm_lower, degreeZero_raise_comm_lower,
    degreeZeroCartan_comm_a1Dag, degreeZeroCartan_comm_a2Dag,
    degreeZeroRaise_comm_a2Dag, degreeZeroLower_comm_a1Dag⟩

end InfoGeometry.Physics.NuclearFiveGradeDegreeZeroSL2
