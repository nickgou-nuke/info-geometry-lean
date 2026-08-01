import Mathlib

/-!
# Finite positive Grassmannian matrix chart and amplituhedron image

This file deliberately formalizes only finite linear-algebra data.  A matrix
with nonnegative maximal minors is used as a concrete chart-level proxy for a
positive Grassmannian point, and `C ↦ C * Z` is the corresponding linear map.
No quotient by row operations, positroid-cell decomposition, canonical form,
boundary residue, or BCFW tiling is asserted here.
-/

namespace InfoGeometry.Canonical

open Matrix

variable {k n m : ℕ}

/-- The maximal minor selected by a map from `Fin k` into the column index set. -/
def maximalMinor (C : Matrix (Fin k) (Fin n) ℝ) (s : Fin k → Fin n) : ℝ :=
  Matrix.det (fun i j => C i (s j))

/-- All selected maximal minors are nonnegative. -/
def HasNonnegativeMaximalMinors (C : Matrix (Fin k) (Fin n) ℝ) : Prop :=
  ∀ s : Fin k → Fin n, StrictMono s → 0 ≤ maximalMinor C s

/-- All selected maximal minors are strictly positive. -/
def HasPositiveMaximalMinors (C : Matrix (Fin k) (Fin n) ℝ) : Prop :=
  ∀ s : Fin k → Fin n, StrictMono s → 0 < maximalMinor C s

/-- A finite matrix-chart version of the nonnegative Grassmannian. -/
def positiveGrassmannianChart : Set (Matrix (Fin k) (Fin n) ℝ) :=
  {C | HasNonnegativeMaximalMinors C}

/-- A finite matrix-chart version of the strictly positive Grassmannian. -/
def positiveGrassmannianInterior : Set (Matrix (Fin k) (Fin n) ℝ) :=
  {C | HasPositiveMaximalMinors C}

theorem mem_positiveGrassmannianChart_iff
    (C : Matrix (Fin k) (Fin n) ℝ) :
    C ∈ positiveGrassmannianChart (k := k) (n := n) ↔
      HasNonnegativeMaximalMinors C := Iff.rfl

theorem mem_positiveGrassmannianInterior_iff
    (C : Matrix (Fin k) (Fin n) ℝ) :
    C ∈ positiveGrassmannianInterior (k := k) (n := n) ↔
      HasPositiveMaximalMinors C := Iff.rfl

theorem positiveGrassmannianInterior_subset_chart :
    positiveGrassmannianInterior (k := k) (n := n) ⊆
      positiveGrassmannianChart (k := k) (n := n) := by
  intro C hC s hs
  exact le_of_lt (hC s hs)

/-- The finite amplituhedron map associated with external-data matrix `Z`. -/
def amplituhedronMap
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) : Matrix (Fin k) (Fin m) ℝ :=
  C * Z

/-- The image of the nonnegative matrix chart under `C ↦ C * Z`. -/
def amplituhedronImage
    (Z : Matrix (Fin n) (Fin m) ℝ) : Set (Matrix (Fin k) (Fin m) ℝ) :=
  amplituhedronMap Z '' positiveGrassmannianChart (k := k) (n := n)

theorem amplituhedronMap_apply
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) :
    amplituhedronMap Z C = C * Z := rfl

theorem amplituhedronMap_add
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (C₁ C₂ : Matrix (Fin k) (Fin n) ℝ) :
    amplituhedronMap Z (C₁ + C₂) =
      amplituhedronMap Z C₁ + amplituhedronMap Z C₂ := by
  simp [amplituhedronMap, Matrix.add_mul]

theorem amplituhedronMap_smul
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (a : ℝ) (C : Matrix (Fin k) (Fin n) ℝ) :
    amplituhedronMap Z (a • C) = a • amplituhedronMap Z C := by
  simp [amplituhedronMap, Matrix.smul_mul]

theorem continuous_amplituhedronMap
    (Z : Matrix (Fin n) (Fin m) ℝ) :
    Continuous (amplituhedronMap (k := k) (n := n) (m := m) Z) := by
  exact (continuous_id :
    Continuous (fun C : Matrix (Fin k) (Fin n) ℝ => C)).matrix_mul
      (continuous_const :
        Continuous (fun _ : Matrix (Fin k) (Fin n) ℝ => Z))

theorem mem_amplituhedronImage_iff
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (Y : Matrix (Fin k) (Fin m) ℝ) :
    Y ∈ amplituhedronImage (k := k) (n := n) (m := m) Z ↔
      ∃ C, C ∈ positiveGrassmannianChart (k := k) (n := n) ∧
        amplituhedronMap Z C = Y := by
  rfl

theorem amplituhedronMap_mem_image
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ)
    (hC : C ∈ positiveGrassmannianChart (k := k) (n := n)) :
    amplituhedronMap Z C ∈ amplituhedronImage (k := k) (n := n) (m := m) Z := by
  exact ⟨C, hC, rfl⟩

theorem amplituhedronImage_subset_range
    (Z : Matrix (Fin n) (Fin m) ℝ) :
    amplituhedronImage (k := k) (n := n) (m := m) Z ⊆
      Set.range (amplituhedronMap (k := k) (n := n) (m := m) Z) := by
  rintro Y ⟨C, _, rfl⟩
  exact ⟨C, rfl⟩

end InfoGeometry.Canonical
