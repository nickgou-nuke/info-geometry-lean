import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Retained chiral operator words and real five-grade closure

This owner lives in an associative real operator algebra.  Quadratic words
are retained as products; they are not identified with their Zorn shadow.
The five-grade routing record contains obligations for a concrete realization;
it does not assert those obligations without proof.
-/

namespace InfoGeometry.OperatorAlgebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

def HasOperatorGrade (N X : A) (k : ℤ) : Prop :=
  N * X - X * N = (k : ℝ) • X

def operatorCommutator (X Y : A) : A := X * Y - Y * X

def operatorAnticommutator (X Y : A) : A := X * Y + Y * X

theorem grade_mul {N X Y : A} {r s : ℤ}
    (hX : HasOperatorGrade N X r)
    (hY : HasOperatorGrade N Y s) :
    HasOperatorGrade N (X * Y) (r + s) := by
  unfold HasOperatorGrade at hX hY ⊢
  calc
    N * (X * Y) - (X * Y) * N =
        (N * X - X * N) * Y + X * (N * Y - Y * N) := by
          noncomm_ring
    _ = ((r : ℝ) • X) * Y + X * ((s : ℝ) • Y) := by rw [hX, hY]
    _ = ((r + s : ℤ) : ℝ) • (X * Y) := by
      rw [smul_mul_assoc, mul_smul_comm, ← add_smul, Int.cast_add]

theorem grade_add {N X Y : A} {r : ℤ}
    (hX : HasOperatorGrade N X r)
    (hY : HasOperatorGrade N Y r) :
    HasOperatorGrade N (X + Y) r := by
  unfold HasOperatorGrade at hX hY ⊢
  calc
    N * (X + Y) - (X + Y) * N =
        (N * X - X * N) + (N * Y - Y * N) := by noncomm_ring
    _ = (r : ℝ) • X + (r : ℝ) • Y := by rw [hX, hY]
    _ = (r : ℝ) • (X + Y) := by rw [smul_add]

theorem grade_sub {N X Y : A} {r : ℤ}
    (hX : HasOperatorGrade N X r)
    (hY : HasOperatorGrade N Y r) :
    HasOperatorGrade N (X - Y) r := by
  unfold HasOperatorGrade at hX hY ⊢
  calc
    N * (X - Y) - (X - Y) * N =
        (N * X - X * N) - (N * Y - Y * N) := by noncomm_ring
    _ = (r : ℝ) • X - (r : ℝ) • Y := by rw [hX, hY]
    _ = (r : ℝ) • (X - Y) := by rw [smul_sub]

theorem grade_smul {N X : A} {r : ℤ} (c : ℝ)
    (hX : HasOperatorGrade N X r) :
    HasOperatorGrade N (c • X) r := by
  unfold HasOperatorGrade at hX ⊢
  calc
    N * (c • X) - (c • X) * N =
        c • (N * X - X * N) := by
          rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    _ = c • ((r : ℝ) • X) := by rw [hX]
    _ = (r : ℝ) • (c • X) := by rw [smul_comm]

theorem grade_commutator {N X Y : A} {r s : ℤ}
    (hX : HasOperatorGrade N X r)
    (hY : HasOperatorGrade N Y s) :
    HasOperatorGrade N (operatorCommutator X Y) (r + s) := by
  change HasOperatorGrade N (X * Y - Y * X) (r + s)
  apply grade_sub (grade_mul hX hY)
  simpa [add_comm] using grade_mul hY hX

theorem grade_anticommutator {N X Y : A} {r s : ℤ}
    (hX : HasOperatorGrade N X r)
    (hY : HasOperatorGrade N Y s) :
    HasOperatorGrade N (operatorAnticommutator X Y) (r + s) := by
  change HasOperatorGrade N (X * Y + Y * X) (r + s)
  apply grade_add (grade_mul hX hY)
  simpa [add_comm] using grade_mul hY hX

def gradeSubmodule (N : A) (k : ℤ) : Submodule ℝ A where
  carrier := {X | HasOperatorGrade N X k}
  zero_mem' := by simp [HasOperatorGrade]
  add_mem' := by
    intro X Y hX hY
    exact grade_add hX hY
  smul_mem' := by
    intro c X hX
    exact grade_smul c hX

theorem mem_gradeSubmodule_iff (N X : A) (k : ℤ) :
    X ∈ gradeSubmodule N k ↔ HasOperatorGrade N X k := Iff.rfl

inductive FiveGrade
  | negTwo
  | negOne
  | zero
  | posOne
  | posTwo
deriving DecidableEq

def FiveGrade.value : FiveGrade → ℤ
  | .negTwo => -2
  | .negOne => -1
  | .zero => 0
  | .posOne => 1
  | .posTwo => 2

structure RetainedChiralOperators (N : A) where
  positive : Fin 3 → A
  negative : Fin 3 → A
  plusProjector : A
  minusProjector : A
  positive_grade : ∀ i, HasOperatorGrade N (positive i) 1
  negative_grade : ∀ i, HasOperatorGrade N (negative i) (-1)
  plusProjector_grade : HasOperatorGrade N plusProjector 0
  minusProjector_grade : HasOperatorGrade N minusProjector 0

namespace RetainedChiralOperators

variable {N : A} (D : RetainedChiralOperators N)

def positiveQuadratic (i j : Fin 3) : A := D.positive i * D.positive j

def negativeQuadratic (i j : Fin 3) : A := D.negative i * D.negative j

def mixedPositiveNegative (i j : Fin 3) : A := D.positive i * D.negative j

def mixedNegativePositive (i j : Fin 3) : A := D.negative i * D.positive j

theorem positiveQuadratic_grade (i j : Fin 3) :
    HasOperatorGrade N (D.positiveQuadratic i j) 2 := by
  exact grade_mul (D.positive_grade i) (D.positive_grade j)

theorem negativeQuadratic_grade (i j : Fin 3) :
    HasOperatorGrade N (D.negativeQuadratic i j) (-2) := by
  simpa only [Int.neg_add] using
    (grade_mul (D.negative_grade i) (D.negative_grade j))

theorem mixedPositiveNegative_grade (i j : Fin 3) :
    HasOperatorGrade N (D.mixedPositiveNegative i j) 0 := by
  simpa using grade_mul (D.positive_grade i) (D.negative_grade j)

theorem mixedNegativePositive_grade (i j : Fin 3) :
    HasOperatorGrade N (D.mixedNegativePositive i j) 0 := by
  simpa using grade_mul (D.negative_grade i) (D.positive_grade j)

def sector (g : FiveGrade) : Set A :=
  match g with
  | .negTwo => Set.range (fun ij : Fin 3 × Fin 3 =>
      D.negativeQuadratic ij.1 ij.2)
  | .negOne => Set.range D.negative
  | .zero =>
      ({D.plusProjector, D.minusProjector} : Set A) ∪
        Set.range (fun ij : Fin 3 × Fin 3 =>
          D.mixedPositiveNegative ij.1 ij.2) ∪
        Set.range (fun ij : Fin 3 × Fin 3 =>
          D.mixedNegativePositive ij.1 ij.2)
  | .posOne => Set.range D.positive
  | .posTwo => Set.range (fun ij : Fin 3 × Fin 3 =>
      D.positiveQuadratic ij.1 ij.2)

def sectorSubmodule (g : FiveGrade) : Submodule ℝ A :=
  Submodule.span ℝ (D.sector g)

theorem sector_negTwo_le_gradeSubmodule :
    D.sectorSubmodule .negTwo ≤ gradeSubmodule N (-2) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨ij, rfl⟩
  exact D.negativeQuadratic_grade ij.1 ij.2

theorem sector_negOne_le_gradeSubmodule :
    D.sectorSubmodule .negOne ≤ gradeSubmodule N (-1) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact D.negative_grade i

theorem sector_posOne_le_gradeSubmodule :
    D.sectorSubmodule .posOne ≤ gradeSubmodule N 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact D.positive_grade i

theorem sector_posTwo_le_gradeSubmodule :
    D.sectorSubmodule .posTwo ≤ gradeSubmodule N 2 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨ij, rfl⟩
  exact D.positiveQuadratic_grade ij.1 ij.2

theorem sector_zero_le_gradeSubmodule :
    D.sectorSubmodule .zero ≤ gradeSubmodule N 0 := by
  refine Submodule.span_le.2 ?_
  intro X hX
  change X ∈ D.sector .zero at hX
  simp only [sector, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_range] at hX
  rcases hX with hX | ⟨ij, hX⟩
  · rcases hX with hX | ⟨ij, hX⟩
    · rcases hX with hX | hX
      · rw [hX]
        exact D.plusProjector_grade
      · rw [hX]
        exact D.minusProjector_grade
    · rw [← hX]
      exact D.mixedPositiveNegative_grade ij.1 ij.2
  · rw [← hX]
    exact D.mixedNegativePositive_grade ij.1 ij.2

theorem positive_mem_gradeSubmodule (i : Fin 3) :
    D.positive i ∈ gradeSubmodule N 1 :=
  D.positive_grade i

theorem negative_mem_gradeSubmodule (i : Fin 3) :
    D.negative i ∈ gradeSubmodule N (-1) :=
  D.negative_grade i

theorem positiveQuadratic_mem_gradeSubmodule (i j : Fin 3) :
    D.positiveQuadratic i j ∈ gradeSubmodule N 2 :=
  D.positiveQuadratic_grade i j

theorem negativeQuadratic_mem_gradeSubmodule (i j : Fin 3) :
    D.negativeQuadratic i j ∈ gradeSubmodule N (-2) :=
  D.negativeQuadratic_grade i j

theorem mixedPositiveNegative_mem_gradeSubmodule (i j : Fin 3) :
    D.mixedPositiveNegative i j ∈ gradeSubmodule N 0 :=
  D.mixedPositiveNegative_grade i j

theorem mixedNegativePositive_mem_gradeSubmodule (i j : Fin 3) :
    D.mixedNegativePositive i j ∈ gradeSubmodule N 0 :=
  D.mixedNegativePositive_grade i j

theorem plusProjector_mem_gradeSubmodule :
    D.plusProjector ∈ gradeSubmodule N 0 :=
  D.plusProjector_grade

theorem minusProjector_mem_gradeSubmodule :
    D.minusProjector ∈ gradeSubmodule N 0 :=
  D.minusProjector_grade

end RetainedChiralOperators

end InfoGeometry.OperatorAlgebra
