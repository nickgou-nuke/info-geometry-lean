import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KantorPeirceFiveGrading
import InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules

/-!
# Concrete Cartan grades as Kantor--Peirce commutator components

The centered total-occupation grading element in the two-mode CAR model is a
tripotent matrix.  The concrete relation

`[H,X] = k X`

is therefore exactly the generic `IsCommutatorComponent` relation owned by
`KantorPeirceFiveGrading`, specialized to the tripotent `H`.

This is a genuine identification of the concrete Cartan eigenspaces with the
repository's associative Kantor/Peirce component interface.  It does not yet
identify them with the separate generic Freudenthal carrier.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeKantorComponentBridge

open Matrix
open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules

local notation "M4R" =>
  InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R

/-- The centered occupation grading matrix is tripotent. -/
theorem gradingOperator_isTripotent :
    IsTripotent gradingOperator := by
  unfold IsTripotent
  rw [gradingOperator_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal,
      Matrix.one_apply]

/-- The two commutator definitions agree exactly. -/
theorem commutatorAction_gradingOperator (X : M4R) :
    commutatorAction gradingOperator X = comm gradingOperator X := rfl

/-- Concrete integer grade membership is exactly the generic real-weight
commutator-component predicate. -/
theorem hasGrade_iff_isCommutatorComponent
    (k : ℤ) (X : M4R) :
    HasGrade k X ↔
      IsCommutatorComponent gradingOperator X (k : ℝ) := by
  rfl

/-- Bundled grade-space membership has the same generic interpretation. -/
theorem mem_gradeSpace_iff_isCommutatorComponent
    (k : ℤ) (X : M4R) :
    X ∈ gradeSpace k ↔
      IsCommutatorComponent gradingOperator X (k : ℝ) := by
  rfl

/-- The generic product-component theorem applies directly to the concrete
tripotent grading. -/
theorem product_isCommutatorComponent
    {k l : ℤ} {X Y : M4R}
    (hX : X ∈ gradeSpace k)
    (hY : Y ∈ gradeSpace l) :
    IsCommutatorComponent gradingOperator (X * Y)
      ((k : ℝ) + (l : ℝ)) := by
  exact commutatorAction_product_component
    ((hasGrade_iff_isCommutatorComponent k X).1 hX)
    ((hasGrade_iff_isCommutatorComponent l Y).1 hY)

/-- The five named lanes are exact tripotent commutator components. -/
theorem named_kantor_component_packet :
    IsTripotent gradingOperator ∧
      IsCommutatorComponent gradingOperator pairAnnihilation (-2 : ℝ) ∧
      IsCommutatorComponent gradingOperator a1 (-1 : ℝ) ∧
      IsCommutatorComponent gradingOperator (comm a1 a1Dag) 0 ∧
      IsCommutatorComponent gradingOperator a1Dag 1 ∧
      IsCommutatorComponent gradingOperator pairCreation 2 := by
  refine ⟨gradingOperator_isTripotent, ?_, ?_, ?_, ?_, ?_⟩
  · convert (hasGrade_iff_isCommutatorComponent (-2) pairAnnihilation).1
      pairAnnihilation_grade using 1 <;> norm_num
  · convert (hasGrade_iff_isCommutatorComponent (-1) a1).1 a1_grade using 1 <;>
      norm_num
  · convert (hasGrade_iff_isCommutatorComponent 0 (comm a1 a1Dag)).1
      mixed_a1_a1Dag_grade_zero using 1 <;> norm_num
  · convert (hasGrade_iff_isCommutatorComponent 1 a1Dag).1 a1Dag_grade using 1 <;>
      norm_num
  · convert (hasGrade_iff_isCommutatorComponent 2 pairCreation).1
      pairCreation_grade using 1 <;> norm_num

end InfoGeometry.Physics.NuclearFiveGradeKantorComponentBridge
