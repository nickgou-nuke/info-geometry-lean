import InfoGeometry.Projective.ExteriorPowerPluckerBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PositiveGrassmannianAmplituhedron

/-!
# The finite `Gr(2,4)` Plücker readout for matrix representatives

This owner connects a concrete 2-by-4 matrix representative to the existing
exterior/Klein Plücker carrier.  It proves the quadratic Plücker relation only;
entrywise nonnegativity and strict positive-minor conditions remain separate
data and are not conflated with this equation.
-/

namespace InfoGeometry.Projective.MatrixPluckerPositiveBridge

open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Canonical

abbrev Matrix2x4 := Matrix (Fin 2) (Fin 4) ℝ

def rowVec4 (M : Matrix2x4) (r : Fin 2) : Vec4 :=
  fun i => match i with
    | I4.t => M r 0
    | I4.x => M r 1
    | I4.y => M r 2
    | I4.z => M r 3

/-- The six ordered 2-by-2 minors of the two rows of `M`. -/
def matrixPluckerCoords (M : Matrix2x4) : InfoGeometry.Algebra.FiniteSpin.Vec6R :=
  pluckerCoords (rowVec4 M 0) (rowVec4 M 1)

def swapRows (M : Matrix2x4) : Matrix2x4 :=
  fun i j => if i = 0 then M 1 j else M 0 j

def scaleFirstRow (l : ℝ) (M : Matrix2x4) : Matrix2x4 :=
  fun i j => if i = 0 then l * M i j else M i j

def scaleSecondRow (l : ℝ) (M : Matrix2x4) : Matrix2x4 :=
  fun i j => if i = 1 then l * M i j else M i j

def scaleRows (l₁ l₂ : ℝ) (M : Matrix2x4) : Matrix2x4 :=
  scaleSecondRow l₂ (scaleFirstRow l₁ M)

@[simp] theorem matrixPluckerCoords_apply (M : Matrix2x4) (i : Fin 6) :
    matrixPluckerCoords M i =
      match i with
      | 0 => M 0 0 * M 1 1 - M 0 1 * M 1 0
      | 1 => M 0 0 * M 1 2 - M 0 2 * M 1 0
      | 2 => M 0 0 * M 1 3 - M 0 3 * M 1 0
      | 3 => M 0 1 * M 1 2 - M 0 2 * M 1 1
      | 4 => M 0 1 * M 1 3 - M 0 3 * M 1 1
      | 5 => M 0 2 * M 1 3 - M 0 3 * M 1 2 := by
  fin_cases i <;> rfl

theorem matrixPluckerCoords_klein_relation (M : Matrix2x4) :
    matrixPluckerCoords M 0 * matrixPluckerCoords M 5
      - matrixPluckerCoords M 1 * matrixPluckerCoords M 4
      + matrixPluckerCoords M 2 * matrixPluckerCoords M 3 = 0 := by
  exact pluckerCoords_on_klein (rowVec4 M 0) (rowVec4 M 1)

private theorem maximalMinor_fin2 (M : Matrix2x4) (a b : Fin 4) :
    maximalMinor M ![a, b] = M 0 a * M 1 b - M 0 b * M 1 a := by
  unfold maximalMinor
  calc
    Matrix.det (fun i j => M i (![a, b] j)) =
        (fun i j => M i (![a, b] j)) 0 0 *
          (fun i j => M i (![a, b] j)) 1 1 -
          (fun i j => M i (![a, b] j)) 0 1 *
          (fun i j => M i (![a, b] j)) 1 0 := Matrix.det_fin_two _
    _ = M 0 a * M 1 b - M 0 b * M 1 a := by simp

theorem matrixPluckerCoords_swapRows (M : Matrix2x4) :
    matrixPluckerCoords (swapRows M) =
      fun i => -matrixPluckerCoords M i := by
  funext i
  fin_cases i <;>
    simp [matrixPluckerCoords, swapRows, rowVec4, pluckerCoords] <;> ring

theorem matrixPluckerCoords_scaleFirstRow (l : ℝ) (M : Matrix2x4) :
    matrixPluckerCoords (scaleFirstRow l M) =
      fun i => l * matrixPluckerCoords M i := by
  funext i
  fin_cases i <;>
    simp [matrixPluckerCoords, scaleFirstRow, rowVec4, pluckerCoords] <;> ring

theorem matrixPluckerCoords_scaleSecondRow (l : ℝ) (M : Matrix2x4) :
    matrixPluckerCoords (scaleSecondRow l M) =
      fun i => l * matrixPluckerCoords M i := by
  funext i
  fin_cases i <;>
    simp [matrixPluckerCoords, scaleSecondRow, rowVec4, pluckerCoords] <;> ring

theorem matrixPluckerCoords_scaleRows (l₁ l₂ : ℝ) (M : Matrix2x4) :
    matrixPluckerCoords (scaleRows l₁ l₂ M) =
      fun i => (l₁ * l₂) * matrixPluckerCoords M i := by
  rw [scaleRows, matrixPluckerCoords_scaleSecondRow]
  funext i
  rw [matrixPluckerCoords_scaleFirstRow]
  ring

/-- Entrywise nonnegativity of the six Plücker minors, kept separate from the
quadratic relation. -/
def MatrixPluckerNonnegative (M : Matrix2x4) : Prop :=
  ∀ i, 0 ≤ matrixPluckerCoords M i

/-- Strict positivity of all six ordered Plücker coordinates. -/
def MatrixPluckerPositive (M : Matrix2x4) : Prop :=
  ∀ i, 0 < matrixPluckerCoords M i

theorem matrixPlucker_nonnegative_readout
    (M : Matrix2x4) (hM : MatrixPluckerNonnegative M) (i : Fin 6) :
    0 ≤ matrixPluckerCoords M i :=
  hM i

private theorem maximalMinor_nonnegative_of_matrixPluckerNonnegative
    (M : Matrix2x4) (hM : MatrixPluckerNonnegative M)
    (a b : Fin 4) (hab : a < b) :
    0 ≤ maximalMinor M ![a, b] := by
  rw [maximalMinor_fin2]
  fin_cases a <;> fin_cases b <;> try norm_num at hab
  all_goals
    first
    | exact (by simpa [MatrixPluckerNonnegative, matrixPluckerCoords_apply] using hM 0)
    | exact (by simpa [MatrixPluckerNonnegative, matrixPluckerCoords_apply] using hM 1)
    | exact (by simpa [MatrixPluckerNonnegative, matrixPluckerCoords_apply] using hM 2)
    | exact (by simpa [MatrixPluckerNonnegative, matrixPluckerCoords_apply] using hM 3)
    | exact (by simpa [MatrixPluckerNonnegative, matrixPluckerCoords_apply] using hM 4)
    | exact (by simpa [MatrixPluckerNonnegative, matrixPluckerCoords_apply] using hM 5)

private theorem maximalMinor_positive_of_matrixPluckerPositive
    (M : Matrix2x4) (hM : MatrixPluckerPositive M)
    (a b : Fin 4) (hab : a < b) :
    0 < maximalMinor M ![a, b] := by
  rw [maximalMinor_fin2]
  fin_cases a <;> fin_cases b <;> try norm_num at hab
  all_goals
    first
    | exact (by simpa [MatrixPluckerPositive, matrixPluckerCoords_apply] using hM 0)
    | exact (by simpa [MatrixPluckerPositive, matrixPluckerCoords_apply] using hM 1)
    | exact (by simpa [MatrixPluckerPositive, matrixPluckerCoords_apply] using hM 2)
    | exact (by simpa [MatrixPluckerPositive, matrixPluckerCoords_apply] using hM 3)
    | exact (by simpa [MatrixPluckerPositive, matrixPluckerCoords_apply] using hM 4)
    | exact (by simpa [MatrixPluckerPositive, matrixPluckerCoords_apply] using hM 5)

/-! The canonical chart owner quantifies over all strict-monotone column
    selections.  For `Gr(2,4)`, its six standard selections are exactly the
    six coordinates used by `matrixPluckerCoords`. -/

theorem positiveGrassmannianInterior_mem_matrixPluckerPositive
    (M : Matrix2x4)
    (hM : M ∈ positiveGrassmannianInterior (k := 2) (n := 4)) :
    MatrixPluckerPositive M := by
  intro i
  fin_cases i
  · have h := hM ![0, 1] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 0 1] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![0, 2] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 0 2] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![0, 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 0 3] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![1, 2] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 1 2] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![1, 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 1 3] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![2, 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 2 3] at h
    rw [matrixPluckerCoords_apply]
    exact h

theorem matrixPluckerPositive_mem_positiveGrassmannianInterior
    (M : Matrix2x4)
    (hM : MatrixPluckerPositive M) :
    M ∈ positiveGrassmannianInterior (k := 2) (n := 4) := by
  intro s hs
  let a := s 0
  let b := s 1
  have hab : a < b := by simpa [a, b] using hs (by decide)
  have hs_eq : s = ![a, b] := by
    funext j
    fin_cases j <;> simp [a, b]
  rw [hs_eq]
  exact maximalMinor_positive_of_matrixPluckerPositive M hM a b hab

theorem matrixPluckerNonnegative_mem_positiveGrassmannianChart
    (M : Matrix2x4)
    (hM : MatrixPluckerNonnegative M) :
    M ∈ positiveGrassmannianChart (k := 2) (n := 4) := by
  intro s hs
  let a := s 0
  let b := s 1
  have hab : a < b := by simpa [a, b] using hs (by decide)
  have hs_eq : s = ![a, b] := by
    funext j
    fin_cases j <;> simp [a, b]
  rw [hs_eq]
  exact maximalMinor_nonnegative_of_matrixPluckerNonnegative M hM a b hab

theorem positiveGrassmannianChart_mem_matrixPluckerNonnegative
    (M : Matrix2x4)
    (hM : M ∈ positiveGrassmannianChart (k := 2) (n := 4)) :
    MatrixPluckerNonnegative M := by
  intro i
  fin_cases i
  · have h := hM ![0, 1] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 0 1] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![0, 2] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 0 2] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![0, 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 0 3] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![1, 2] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 1 2] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![1, 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 1 3] at h
    rw [matrixPluckerCoords_apply]
    exact h
  · have h := hM ![2, 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [maximalMinor_fin2 M 2 3] at h
    rw [matrixPluckerCoords_apply]
    exact h

theorem matrixPlucker_positive_scaleFirstRow
    (l : ℝ) (hl : 0 < l) (M : Matrix2x4)
    (hM : MatrixPluckerPositive M) :
    MatrixPluckerPositive (scaleFirstRow l M) := by
  intro i
  rw [matrixPluckerCoords_scaleFirstRow]
  exact mul_pos hl (hM i)

theorem matrixPlucker_positive_scaleSecondRow
    (l : ℝ) (hl : 0 < l) (M : Matrix2x4)
    (hM : MatrixPluckerPositive M) :
    MatrixPluckerPositive (scaleSecondRow l M) := by
  intro i
  rw [matrixPluckerCoords_scaleSecondRow]
  exact mul_pos hl (hM i)

theorem matrixPlucker_positive_scaleRows
    (l₁ l₂ : ℝ) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (M : Matrix2x4)
    (hM : MatrixPluckerPositive M) :
    MatrixPluckerPositive (scaleRows l₁ l₂ M) := by
  intro i
  rw [matrixPluckerCoords_scaleRows]
  exact mul_pos (mul_pos hl₁ hl₂) (hM i)

theorem matrixPlucker_nonnegative_scaleRows
    (l₁ l₂ : ℝ) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (M : Matrix2x4)
    (hM : MatrixPluckerNonnegative M) :
    MatrixPluckerNonnegative (scaleRows l₁ l₂ M) := by
  intro i
  rw [matrixPluckerCoords_scaleRows]
  exact mul_nonneg (mul_nonneg hl₁ hl₂) (hM i)

end InfoGeometry.Projective.MatrixPluckerPositiveBridge
