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

local notation "a1" => InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1
local notation "a2" => InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2
local notation "a1Dag" => InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag
local notation "a2Dag" => InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag
local notation "pairCreation" => InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
local notation "pairAnnihilation" => InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation

/-- The custom readout is the native associative Lie bracket. -/
@[simp] theorem lie_bracket_eq_comm (X Y : M4R) :
    ⁅X, Y⁆ = NuclearTwoModeFiveGradeLieModel.comm X Y := rfl

/-- Additivity of the adjoint grade operator. -/
theorem comm_add_right (X Y Z : M4R) :
    NuclearTwoModeFiveGradeLieModel.comm X (Y + Z) =
      NuclearTwoModeFiveGradeLieModel.comm X Y + NuclearTwoModeFiveGradeLieModel.comm X Z := by
  simp [NuclearTwoModeFiveGradeLieModel.comm, mul_add, add_mul]
  abel

/-- Grade-`k` adjoint eigenspace. -/
def gradeSpace (k : ℤ) : Submodule ℝ M4R where
  carrier := {X | HasGrade k X}
  zero_mem' := by
    simp [HasGrade, NuclearTwoModeFiveGradeLieModel.comm]
  add_mem' := by
    intro X Y hX hY
    change HasGrade k (X + Y)
    unfold HasGrade at hX hY ⊢
    rw [comm_add_right, hX, hY, smul_add]
  smul_mem' := by
    intro c X hX
    change HasGrade k (c • X)
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
  change HasGrade (k + l) (NuclearTwoModeFiveGradeLieModel.comm X Y)
  exact comm_hasGrade hX hY

/-- Bilinear bracket map between two fixed grades. -/
def gradeBracket (k l : ℤ) :
    gradeSpace k →ₗ[ℝ] gradeSpace l →ₗ[ℝ] gradeSpace (k + l) :=
  LinearMap.mk₂ ℝ
    (fun X Y => ⟨NuclearTwoModeFiveGradeLieModel.comm X.1 Y.1, comm_hasGrade X.2 Y.2⟩)
    (fun X₁ X₂ Y => by
      apply Subtype.ext
      simp [NuclearTwoModeFiveGradeLieModel.comm, add_mul, mul_add]
      abel)
    (fun c X Y => by
      apply Subtype.ext
      exact comm_smul_left c X.1 Y.1)
    (fun X Y₁ Y₂ => by
      apply Subtype.ext
      simp [NuclearTwoModeFiveGradeLieModel.comm, add_mul, mul_add]
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
  exact ⟨by simpa [gradeSpace] using pairAnnihilation_grade,
    by simpa [gradeSpace] using a1_grade,
    by simpa [gradeSpace] using a2_grade,
    by simpa [gradeSpace] using mixed_a1_a1Dag_grade_zero,
    by simpa [gradeSpace] using a1Dag_grade,
    by simpa [gradeSpace] using a2Dag_grade,
    by simpa [gradeSpace] using pairCreation_grade⟩

/-- The concrete five-grade API as bundled submodules plus native bracket
closure. -/
theorem bundled_five_grade_packet :
    pairAnnihilation ∈ gradeSpace (-2) ∧
      a1 ∈ gradeSpace (-1) ∧
      comm a1 a1Dag ∈ gradeSpace 0 ∧
      a1Dag ∈ gradeSpace 1 ∧
      pairCreation ∈ gradeSpace 2 ∧
      ⁅pairCreation, pairAnnihilation⁆ ∈ gradeSpace 0 := by
  refine ⟨by simpa [gradeSpace] using pairAnnihilation_grade,
    by simpa [gradeSpace] using a1_grade,
    by simpa [gradeSpace] using mixed_a1_a1Dag_grade_zero,
    by simpa [gradeSpace] using a1Dag_grade,
    by simpa [gradeSpace] using pairCreation_grade, ?_⟩
  simpa using lie_mem_grade_add pairCreation_grade pairAnnihilation_grade

end InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
