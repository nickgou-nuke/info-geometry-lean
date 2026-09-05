import Mathlib
import InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel

/-!
# Bundled eigenspaces for the concrete nuclear five-grading

The unbundled relation `[H,X] = kX` from the two-mode CAR model is packaged as
a Mathlib `Submodule`. The matrix commutator adds weights, giving a reusable
bracket map from grade `k` and grade `l` into grade `k+l`.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules

open Matrix
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR

/-- The custom readout is the native associative Lie bracket. -/
@[simp] theorem lie_bracket_eq_comm (X Y : M4R) :
    ⁅X, Y⁆ = comm X Y := rfl

/-- Additivity of the adjoint grade operator. -/
theorem comm_add_right (X Y Z : M4R) :
    comm X (Y + Z) = comm X Y + comm X Z := by
  simp [comm, mul_add, add_mul]
  abel

/-- Grade-`k` adjoint eigenspace. -/
def gradeSpace (k : ℤ) : Submodule ℝ M4R where
  carrier := {X | HasGrade k X}
  zero_mem' := by
    simp [HasGrade, comm]
  add_mem' := by
    intro X Y hX hY
    unfold HasGrade at hX hY ⊢
    rw [comm_add_right, hX, hY, smul_add]
  smul_mem' := by
    intro c X hX
    unfold HasGrade at hX ⊢
    rw [comm_smul_right, hX]
    simp [smul_smul, mul_comm]

@[simp] theorem mem_gradeSpace (k : ℤ) (X : M4R) :
    X ∈ gradeSpace k ↔ HasGrade k X := Iff.rfl

/-- Native bracket closure of the grade eigenspaces. -/
theorem lie_mem_grade_add
    {k l : ℤ} {X Y : M4R}
    (hX : X ∈ gradeSpace k)
    (hY : Y ∈ gradeSpace l) :
    ⁅X, Y⁆ ∈ gradeSpace (k + l) := by
  change HasGrade (k + l) (comm X Y)
  exact comm_hasGrade hX hY

/-- Bilinear bracket map between two fixed grades. -/
def gradeBracket (k l : ℤ) :
    gradeSpace k →ₗ[ℝ] gradeSpace l →ₗ[ℝ] gradeSpace (k + l) :=
  LinearMap.mk₂ ℝ
    (fun X Y => ⟨comm X.1 Y.1, comm_hasGrade X.2 Y.2⟩)
    (fun X₁ X₂ Y => by
      apply Subtype.ext
      simp [comm, add_mul, mul_add]
      abel)
    (fun c X Y => by
      apply Subtype.ext
      exact comm_smul_left c X.1 Y.1)
    (fun X Y₁ Y₂ => by
      apply Subtype.ext
      simp [comm, add_mul, mul_add]
      abel)
    (fun c X Y => by
      apply Subtype.ext
      exact comm_smul_right c X.1 Y.1)

/-- Named extreme and odd generators inhabit the five bundled lanes. -/
theorem named_generators_mem_grade_spaces :
    pairAnnihilation ∈ gradeSpace (-2) ∧
      a1 ∈ gradeSpace (-1) ∧
      a2 ∈ gradeSpace (-1) ∧
      comm a1 a1Dag ∈ gradeSpace 0 ∧
      a1Dag ∈ gradeSpace 1 ∧
      a2Dag ∈ gradeSpace 1 ∧
      pairCreation ∈ gradeSpace 2 := by
  exact ⟨pairAnnihilation_grade, a1_grade, a2_grade,
    mixed_a1_a1Dag_grade_zero, a1Dag_grade, a2Dag_grade,
    pairCreation_grade⟩

/-- The concrete five-grade API as bundled submodules plus native bracket
closure. -/
theorem bundled_five_grade_packet :
    pairAnnihilation ∈ gradeSpace (-2) ∧
      a1 ∈ gradeSpace (-1) ∧
      comm a1 a1Dag ∈ gradeSpace 0 ∧
      a1Dag ∈ gradeSpace 1 ∧
      pairCreation ∈ gradeSpace 2 ∧
      ⁅pairCreation, pairAnnihilation⁆ ∈ gradeSpace 0 := by
  refine ⟨pairAnnihilation_grade, a1_grade,
    mixed_a1_a1Dag_grade_zero, a1Dag_grade, pairCreation_grade, ?_⟩
  simpa using lie_mem_grade_add pairCreation_grade pairAnnihilation_grade

end InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
