import InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure
import InfoGeometry.OperatorAlgebra.FiveGradeActionPreservation
import InfoGeometry.Canonical.Cl55WittLieRouting

/-!
# The matrix-stage carrier of the five-mode Clifford representation

This owner records the canonical carrier equivalence between the recursive
`MatStage 5` realization and the `Cl(5,5)` carrier.  It transports the
associative algebra carrier only; grading operators remain separate data and
are related only by explicit intertwining theorems.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55MatStageCarrierEquiv

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra

abbrev Mat32 := MatStage 5
abbrev RecursiveMatrix := InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5

def matStageToFin32 : Mat32 ≃ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (idxEquivFinPowTwo 5)

theorem matStageToFin32_apply (X : Mat32) :
    matStageToFin32 X =
      Matrix.reindex (idxEquivFinPowTwo 5) (idxEquivFinPowTwo 5) X :=
  rfl

def matStageToRecursiveMatrix : Mat32 ≃ₐ[ℝ] RecursiveMatrix :=
  matStageToFin32.trans fockToRecursiveMatrixAlgEquiv

def matStageToCl55 : Mat32 ≃ₐ[ℝ] Clifford55.Cl55 :=
  matStageToRecursiveMatrix.trans Clifford55.cl55SpinorAlgEquiv.symm

theorem matStageToCl55_injective :
    Function.Injective matStageToCl55 :=
  matStageToCl55.injective

theorem matStageToCl55_map_mul (X Y : Mat32) :
    matStageToCl55 (X * Y) = matStageToCl55 X * matStageToCl55 Y :=
  map_mul matStageToCl55 X Y

theorem matStageToCl55_map_add (X Y : Mat32) :
    matStageToCl55 (X + Y) = matStageToCl55 X + matStageToCl55 Y :=
  map_add matStageToCl55 X Y

theorem matStageToCl55_map_grade_transport
    {N X : Mat32} {k : ℤ}
    (h : HasOperatorGrade N X k) :
    HasOperatorGrade (matStageToCl55 N) (matStageToCl55 X) k := by
  unfold HasOperatorGrade at h ⊢
  have hx := congrArg matStageToCl55 h
  simpa [map_sub, map_mul, map_smul] using hx

def matStageGradeSubmodule (k : ℤ) :
    Submodule ℝ Mat32 :=
  InfoGeometry.OperatorAlgebra.gradeSubmodule
    InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator k

def cl55TransportedMatStageGradeSubmodule (k : ℤ) :
    Submodule ℝ Clifford55.Cl55 :=
  InfoGeometry.OperatorAlgebra.gradeSubmodule
    (matStageToCl55 InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator) k

theorem matStageToCl55_gradeSubmodule_map (k : ℤ) :
    Submodule.map matStageToCl55.toLinearMap (matStageGradeSubmodule k) =
      cl55TransportedMatStageGradeSubmodule k := by
  exact InfoGeometry.OperatorAlgebra.algEquiv_map_gradeSubmodule_of
    matStageToCl55 InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator k

theorem matStage_cl55_grade_transport :
    MapsToGradeBetween
      (fun k : ℤ => (matStageGradeSubmodule k : Set Mat32))
      (fun k : ℤ => (cl55TransportedMatStageGradeSubmodule k : Set Clifford55.Cl55))
      (fun _ : Unit => matStageToCl55)
      (fun _ k => k) := by
  simpa [matStageGradeSubmodule, cl55TransportedMatStageGradeSubmodule] using
    (InfoGeometry.OperatorAlgebra.algEquiv_mapsToGradeSubmoduleBetween
      matStageToCl55 InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator)

theorem matStageToCl55_grade_mem_iff
    {X : Mat32} {k : ℤ} :
    X ∈ matStageGradeSubmodule k ↔
      matStageToCl55 X ∈ cl55TransportedMatStageGradeSubmodule k := by
  simpa [matStageGradeSubmodule, cl55TransportedMatStageGradeSubmodule] using
    (InfoGeometry.OperatorAlgebra.algEquiv_map_mem_gradeSubmodule_between_iff
      matStageToCl55 InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator X k).symm

theorem matStageToCl55_symm_maps_grade
    {Y : Clifford55.Cl55} {k : ℤ}
    (hY : Y ∈ cl55TransportedMatStageGradeSubmodule k) :
    matStageToCl55.symm Y ∈ matStageGradeSubmodule k := by
  apply (matStageToCl55_grade_mem_iff (X := matStageToCl55.symm Y) (k := k)).2
  simpa using hY

theorem cl55ToMatStage_maps_grade_family :
    MapsToGradeBetween
      (fun k : ℤ => (cl55TransportedMatStageGradeSubmodule k : Set Clifford55.Cl55))
      (fun k : ℤ => (matStageGradeSubmodule k : Set Mat32))
      (fun _ : Unit => matStageToCl55.symm)
      (fun _ k => k) := by
  intro _ k Y hY
  exact matStageToCl55_symm_maps_grade hY

def recursiveMatrixGradeSubmodule (k : ℤ) :
    Submodule ℝ RecursiveMatrix :=
  InfoGeometry.OperatorAlgebra.gradeSubmodule
    (matStageToRecursiveMatrix
      InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator) k

theorem matStageToRecursiveMatrix_gradeSubmodule_map (k : ℤ) :
    Submodule.map matStageToRecursiveMatrix.toLinearMap
        (matStageGradeSubmodule k) = recursiveMatrixGradeSubmodule k := by
  exact InfoGeometry.OperatorAlgebra.algEquiv_map_gradeSubmodule_of
    matStageToRecursiveMatrix
      InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator k

theorem matStageToRecursiveMatrix_grade_image (k : ℤ) :
    matStageToRecursiveMatrix.toLinearEquiv ''
        (matStageGradeSubmodule k : Set Mat32) =
      (recursiveMatrixGradeSubmodule k : Set RecursiveMatrix) := by
  change matStageToRecursiveMatrix.toLinearMap ''
      (matStageGradeSubmodule k : Set Mat32) = _
  rw [← Submodule.map_coe]
  exact congrArg (fun P : Submodule ℝ RecursiveMatrix => (P : Set RecursiveMatrix))
    (matStageToRecursiveMatrix_gradeSubmodule_map k)

theorem matStageToRecursiveMatrix_grade_mem_iff
    {X : Mat32} {k : ℤ} :
    X ∈ matStageGradeSubmodule k ↔
      matStageToRecursiveMatrix X ∈ recursiveMatrixGradeSubmodule k := by
  simpa [matStageGradeSubmodule, recursiveMatrixGradeSubmodule] using
    (InfoGeometry.OperatorAlgebra.algEquiv_map_mem_gradeSubmodule_between_iff
      matStageToRecursiveMatrix InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator X k).symm

theorem recursiveMatrixToCl55_grade_image (k : ℤ) :
    Clifford55.cl55SpinorAlgEquiv.symm.toLinearEquiv ''
        (recursiveMatrixGradeSubmodule k : Set RecursiveMatrix) =
      (cl55TransportedMatStageGradeSubmodule k : Set Clifford55.Cl55) := by
  change Clifford55.cl55SpinorAlgEquiv.symm.toLinearMap ''
      (recursiveMatrixGradeSubmodule k : Set RecursiveMatrix) = _
  rw [← Submodule.map_coe]
  exact congrArg (fun P : Submodule ℝ Clifford55.Cl55 =>
      (P : Set Clifford55.Cl55))
    (InfoGeometry.OperatorAlgebra.algEquiv_map_gradeSubmodule_of
      Clifford55.cl55SpinorAlgEquiv.symm
      (matStageToRecursiveMatrix
        InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator) k)

theorem matStage_recursive_grade_transport :
    MapsToGradeBetween
      (fun k : ℤ => (matStageGradeSubmodule k : Set Mat32))
      (fun k : ℤ => (recursiveMatrixGradeSubmodule k : Set RecursiveMatrix))
      (fun _ : Unit => matStageToRecursiveMatrix)
      (fun _ k => k) := by
  simpa [matStageGradeSubmodule, recursiveMatrixGradeSubmodule] using
    (InfoGeometry.OperatorAlgebra.algEquiv_mapsToGradeSubmoduleBetween
      matStageToRecursiveMatrix InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator)

theorem matStage_cl55_grade_transport_via_recursive :
    MapsToGradeBetween
      (fun k : ℤ => (matStageGradeSubmodule k : Set Mat32))
      (fun k : ℤ => (cl55TransportedMatStageGradeSubmodule k : Set Clifford55.Cl55))
      (fun _ : Unit => matStageToCl55)
      (fun _ k => k) := by
  have h₁ := matStage_recursive_grade_transport
  have h₂ :
      MapsToGradeBetween
        (fun k : ℤ => (recursiveMatrixGradeSubmodule k : Set RecursiveMatrix))
        (fun k : ℤ => (cl55TransportedMatStageGradeSubmodule k : Set Clifford55.Cl55))
        (fun _ : Unit => Clifford55.cl55SpinorAlgEquiv.symm)
        (fun _ k => k) := by
    simpa [recursiveMatrixGradeSubmodule, cl55TransportedMatStageGradeSubmodule,
      matStageToCl55] using
      (InfoGeometry.OperatorAlgebra.algEquiv_mapsToGradeSubmoduleBetween
        Clifford55.cl55SpinorAlgEquiv.symm
        (matStageToRecursiveMatrix InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator))
  intro b i X hX
  have hcomp := InfoGeometry.OperatorAlgebra.mapsToGradeBetween_comp_family h₁ h₂
  have hcomp' := hcomp (b, ()) i hX
  simpa [matStageToCl55] using hcomp'

/- The direct Mat32-to-Cl55 carrier equivalence therefore has an exact image
   statement, assembled from the already-owned two-way grade transport. -/
theorem matStageToCl55_grade_image (k : ℤ) :
    matStageToCl55.toLinearEquiv ''
        (matStageGradeSubmodule k : Set Mat32) =
      (cl55TransportedMatStageGradeSubmodule k : Set Clifford55.Cl55) := by
  apply InfoGeometry.OperatorAlgebra.linearEquiv_mapsToGradeBetween_image_eq
    matStageToCl55.toLinearEquiv
    (fun j : ℤ => (matStageGradeSubmodule j : Set Mat32))
    (fun j : ℤ => (cl55TransportedMatStageGradeSubmodule j : Set Clifford55.Cl55))
    (fun j => j) (fun j => j)
  · intro j
    exact matStage_cl55_grade_transport () j
  · intro j
    exact cl55ToMatStage_maps_grade_family () j
  · intro j
    rfl

def transportedCreation55 (i : Fin 5) : Clifford55.Cl55 :=
  matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.creation i)

def transportedAnnihilation55 (i : Fin 5) : Clifford55.Cl55 :=
  matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.annihilation i)

theorem transportedCreation55_grade_one (i : Fin 5) :
    InfoGeometry.OperatorAlgebra.HasOperatorGrade
      (matStageToCl55 InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator)
      (transportedCreation55 i) 1 := by
  apply matStageToCl55_map_grade_transport
  simpa [InfoGeometry.OperatorAlgebra.HasOperatorGrade,
    InfoGeometry.Canonical.Cl55WittLieRouting.bracket] using
    InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator_creation i

theorem transportedAnnihilation55_grade_neg_one (i : Fin 5) :
    InfoGeometry.OperatorAlgebra.HasOperatorGrade
      (matStageToCl55 InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator)
      (transportedAnnihilation55 i) (-1) := by
  apply matStageToCl55_map_grade_transport
  simpa [InfoGeometry.OperatorAlgebra.HasOperatorGrade,
    InfoGeometry.Canonical.Cl55WittLieRouting.bracket] using
    InfoGeometry.Canonical.Cl55WittLieRouting.numberOperator_annihilation i

theorem transportedCreation55_sq (i : Fin 5) :
    transportedCreation55 i * transportedCreation55 i = 0 := by
  change matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.creation i) *
      matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.creation i) = 0
  simpa only [← matStageToCl55_map_mul, map_zero] using
    congrArg matStageToCl55
      (InfoGeometry.Canonical.Cl55WittCAR.creation_sq 5 i)

theorem transportedAnnihilation55_sq (i : Fin 5) :
    transportedAnnihilation55 i * transportedAnnihilation55 i = 0 := by
  change matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.annihilation i) *
      matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.annihilation i) = 0
  simpa only [← matStageToCl55_map_mul, map_zero] using
    congrArg matStageToCl55
      (InfoGeometry.Canonical.Cl55WittCAR.annihilation_sq 5 i)

theorem transportedCreation55_annihilation55_car (i : Fin 5) :
    transportedCreation55 i * transportedAnnihilation55 i +
        transportedAnnihilation55 i * transportedCreation55 i = 1 := by
  change matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.creation i) *
      matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.annihilation i) +
      matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.annihilation i) *
        matStageToCl55 (InfoGeometry.Canonical.Cl55WittCAR.creation i) = 1
  simpa only [← matStageToCl55_map_mul, ← matStageToCl55_map_add, map_one] using
    congrArg matStageToCl55
      (InfoGeometry.Canonical.Cl55WittCAR.same_site_car 5 i)

end InfoGeometry.Clifford.Cl55MatStageCarrierEquiv
