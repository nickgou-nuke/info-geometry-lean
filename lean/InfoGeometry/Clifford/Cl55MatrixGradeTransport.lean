import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv
import InfoGeometry.Nuclear.FiveGradedOperatorTransport

/-! Matrix readout of the native `Cl(5,5)` five-grading.  The grading is
transported through the repository-owned spinor algebra equivalence; no
coordinate formula for the number operator is assumed. -/

noncomputable section
namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra

abbrev SpinorMatrix := Matrix (Fin 32) (Fin 32) ℝ

noncomputable def nativeCl55OperatorFiveGrading :
    InfoGeometry.Nuclear.GradedBathCommutant.OperatorFiveGrading Cl55 where
  gNegTwo := gradeSubmodule numberOperator55 (-2)
  gNegOne := gradeSubmodule numberOperator55 (-1)
  gZero := gradeSubmodule numberOperator55 0
  gPosOne := gradeSubmodule numberOperator55 1
  gPosTwo := gradeSubmodule numberOperator55 2
  negOne_posOne_mem_zero := by
    intro X Y hX hY
    exact grade_commutator hX hY
  posOne_posOne_mem_posTwo := by
    intro X Y hX hY
    exact grade_commutator hX hY
  negOne_negOne_mem_negTwo := by
    intro X Y hX hY
    exact grade_commutator hX hY
  zero_posOne_mem_posOne := by
    intro X Y hX hY
    exact grade_commutator hX hY
  zero_negOne_mem_negOne := by
    intro X Y hX hY
    exact grade_commutator hX hY

noncomputable def matrixCl55OperatorFiveGrading :
    InfoGeometry.Nuclear.GradedBathCommutant.OperatorFiveGrading SpinorMatrix :=
  InfoGeometry.Nuclear.GradedBathCommutant.OperatorFiveGrading.transport
    cl55SpinorAlgEquiv nativeCl55OperatorFiveGrading

def matrixGradeSubmodule (k : ℤ) : Submodule ℝ SpinorMatrix :=
  (gradeSubmodule numberOperator55 k).map cl55SpinorAlgEquiv.toLinearMap

theorem matrixGradeSubmodule_eq_transported (k : ℤ) :
    matrixGradeSubmodule k =
      gradeSubmodule (cl55SpinorAlgEquiv numberOperator55) k := by
  simpa [matrixGradeSubmodule] using
    (InfoGeometry.OperatorAlgebra.algEquiv_map_gradeSubmodule_of
      cl55SpinorAlgEquiv numberOperator55 k)

theorem matrixGrade_mem_iff (k : ℤ) (X : Cl55) :
    cl55SpinorAlgEquiv X ∈ matrixGradeSubmodule k ↔
      X ∈ gradeSubmodule numberOperator55 k := by
  rw [matrixGradeSubmodule_eq_transported]
  exact algEquiv_map_mem_gradeSubmodule_between_iff
    cl55SpinorAlgEquiv numberOperator55 X k

theorem cl55SpinorAlgEquiv_mapsTo_matrixGrade :
    MapsToGradeBetween
      (fun k : ℤ => (gradeSubmodule numberOperator55 k : Set Cl55))
      (fun k : ℤ => (matrixGradeSubmodule k : Set SpinorMatrix))
      (fun _ : Unit => cl55SpinorAlgEquiv)
      (fun _ k => k) := by
  intro _ k X hX
  exact (matrixGrade_mem_iff k X).2 hX

theorem cl55SpinorAlgEquiv_symm_mapsTo_cl55Grade
    {Y : SpinorMatrix} {k : ℤ}
    (hY : Y ∈ matrixGradeSubmodule k) :
    cl55SpinorAlgEquiv.symm Y ∈ gradeSubmodule numberOperator55 k := by
  apply (matrixGrade_mem_iff k (cl55SpinorAlgEquiv.symm Y)).1
  simpa using hY

theorem matrixGrade_mapsTo_cl55SpinorAlgEquiv_symm :
    MapsToGradeBetween
      (fun k : ℤ => (matrixGradeSubmodule k : Set SpinorMatrix))
      (fun k : ℤ => (gradeSubmodule numberOperator55 k : Set Cl55))
      (fun _ : Unit => cl55SpinorAlgEquiv.symm)
      (fun _ k => k) := by
  intro _ k Y hY
  exact cl55SpinorAlgEquiv_symm_mapsTo_cl55Grade hY

/- The two existing transport directions assemble into the exact image
   equality required by the common graded-action interface. -/
theorem cl55SpinorAlgEquiv_grade_image (k : ℤ) :
    cl55SpinorAlgEquiv.toLinearEquiv ''
        (gradeSubmodule numberOperator55 k : Set Cl55) =
      (matrixGradeSubmodule k : Set SpinorMatrix) := by
  apply InfoGeometry.OperatorAlgebra.linearEquiv_mapsToGradeBetween_image_eq
    cl55SpinorAlgEquiv.toLinearEquiv
    (fun j : ℤ => (gradeSubmodule numberOperator55 j : Set Cl55))
    (fun j : ℤ => (matrixGradeSubmodule j : Set SpinorMatrix))
    (fun j => j) (fun j => j)
  · intro j
    intro X hX
    exact cl55SpinorAlgEquiv_mapsTo_matrixGrade () j hX
  · intro j
    intro Y hY
    exact matrixGrade_mapsTo_cl55SpinorAlgEquiv_symm () j hY
  · intro j
    rfl

theorem matrixGrade_mul_mem {k l : ℤ} {X Y : Cl55}
    (hX : X ∈ gradeSubmodule numberOperator55 k)
    (hY : Y ∈ gradeSubmodule numberOperator55 l) :
    cl55SpinorAlgEquiv (X * Y) ∈ matrixGradeSubmodule (k + l) := by
  apply (matrixGrade_mem_iff (k + l) (X * Y)).mpr
  exact grade_mul hX hY

theorem matrixGrade_commutator_mem {k l : ℤ} {X Y : Cl55}
    (hX : X ∈ gradeSubmodule numberOperator55 k)
    (hY : Y ∈ gradeSubmodule numberOperator55 l) :
    cl55SpinorAlgEquiv (X * Y - Y * X) ∈ matrixGradeSubmodule (k + l) := by
  apply (matrixGrade_mem_iff (k + l) (X * Y - Y * X)).mpr
  exact grade_commutator hX hY

theorem matrixGrade_anticommutator_mem {k l : ℤ} {X Y : Cl55}
    (hX : X ∈ gradeSubmodule numberOperator55 k)
    (hY : Y ∈ gradeSubmodule numberOperator55 l) :
    cl55SpinorAlgEquiv (X * Y + Y * X) ∈ matrixGradeSubmodule (k + l) := by
  apply (matrixGrade_mem_iff (k + l) (X * Y + Y * X)).mpr
  exact grade_anticommutator hX hY

end InfoGeometry.Clifford.Clifford55
