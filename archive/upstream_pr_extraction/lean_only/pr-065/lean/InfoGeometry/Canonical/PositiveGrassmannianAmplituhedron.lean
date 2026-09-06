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

/-- Left multiplication changes every maximal minor by the determinant of the
row-operation matrix.  This is the finite matrix form of the `GL(k)` gauge
weight of Plücker coordinates. -/
theorem maximalMinor_left_mul
    (A : Matrix (Fin k) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ)
    (s : Fin k → Fin n) :
    maximalMinor (A * C) s = Matrix.det A * maximalMinor C s := by
  unfold maximalMinor
  let B : Matrix (Fin k) (Fin k) ℝ := fun i j => C i (s j)
  have hmat : (fun i j => (A * C) i (s j)) = A * B := by
    ext i j
    simp [B, Matrix.mul_apply]
  rw [hmat, Matrix.det_mul]

theorem hasPositiveMaximalMinors_left_mul
    (A : Matrix (Fin k) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ)
    (hA : 0 < Matrix.det A)
    (hC : HasPositiveMaximalMinors C) :
    HasPositiveMaximalMinors (A * C) := by
  intro s hs
  rw [maximalMinor_left_mul]
  exact mul_pos hA (hC s hs)

theorem hasNonnegativeMaximalMinors_left_mul
    (A : Matrix (Fin k) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ)
    (hA : 0 ≤ Matrix.det A)
    (hC : HasNonnegativeMaximalMinors C) :
    HasNonnegativeMaximalMinors (A * C) := by
  intro s hs
  rw [maximalMinor_left_mul]
  exact mul_nonneg hA (hC s hs)

theorem positiveGrassmannianInterior_left_mul
    (A : Matrix (Fin k) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ)
    (hA : 0 < Matrix.det A)
    (hC : C ∈ positiveGrassmannianInterior (k := k) (n := n)) :
    A * C ∈ positiveGrassmannianInterior (k := k) (n := n) :=
  hasPositiveMaximalMinors_left_mul A C hA hC

theorem positiveGrassmannianChart_left_mul
    (A : Matrix (Fin k) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ)
    (hA : 0 ≤ Matrix.det A)
    (hC : C ∈ positiveGrassmannianChart (k := k) (n := n)) :
    A * C ∈ positiveGrassmannianChart (k := k) (n := n) :=
  hasNonnegativeMaximalMinors_left_mul A C hA hC

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

/-- The amplituhedron map is equivariant for left row operations. -/
theorem amplituhedronMap_left_mul
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin k) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) :
    amplituhedronMap Z (A * C) = A * amplituhedronMap Z C := by
  simp [amplituhedronMap, Matrix.mul_assoc]

theorem amplituhedronImage_left_mul_mem
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : 0 ≤ Matrix.det A)
    {Y : Matrix (Fin k) (Fin m) ℝ}
    (hY : Y ∈ amplituhedronImage (k := k) (n := n) (m := m) Z) :
    A * Y ∈ amplituhedronImage (k := k) (n := n) (m := m) Z := by
  rcases hY with ⟨C, hC, rfl⟩
  refine ⟨A * C, hasNonnegativeMaximalMinors_left_mul A C hA hC, ?_⟩
  exact amplituhedronMap_left_mul Z A C

theorem amplituhedronImage_left_mul_eq_of_left_inverse
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : 0 ≤ Matrix.det A)
    (hB : 0 ≤ Matrix.det B)
    (hAB : A * B = 1) :
    (fun Y : Matrix (Fin k) (Fin m) ℝ => A * Y) ''
        amplituhedronImage (k := k) (n := n) (m := m) Z =
      amplituhedronImage (k := k) (n := n) (m := m) Z := by
  ext Y
  constructor
  · rintro ⟨Y₀, hY₀, rfl⟩
    exact amplituhedronImage_left_mul_mem Z A hA hY₀
  · intro hY
    refine ⟨B * Y, amplituhedronImage_left_mul_mem Z B hB hY, ?_⟩
    change A * (B * Y) = Y
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]

/-- Right multiplication of the external data commutes with the finite
amplituhedron map. -/
theorem amplituhedronMap_right_mul
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) :
    amplituhedronMap (Z * B) C = amplituhedronMap Z C * B := by
  simp [amplituhedronMap, Matrix.mul_assoc]

theorem amplituhedronImage_right_mul_mem
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ)
    {Y : Matrix (Fin k) (Fin m) ℝ}
    (hY : Y ∈ amplituhedronImage (k := k) (n := n) (m := m) Z) :
    Y * B ∈ amplituhedronImage (k := k) (n := n) (m := m) (Z * B) := by
  rcases hY with ⟨C, hC, rfl⟩
  refine ⟨C, hC, ?_⟩
  exact amplituhedronMap_right_mul Z B C

theorem amplituhedronImage_right_mul_eq
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) :
    amplituhedronImage (k := k) (n := n) (m := m) (Z * B) =
      (fun Y : Matrix (Fin k) (Fin m) ℝ => Y * B) ''
        amplituhedronImage (k := k) (n := n) (m := m) Z := by
  ext Y
  constructor
  · rintro ⟨C, hC, hCY⟩
    refine ⟨amplituhedronMap Z C, ⟨C, hC, rfl⟩, ?_⟩
    rw [← hCY, amplituhedronMap_right_mul]
  · rintro ⟨Y₀, ⟨C, hC, rfl⟩, rfl⟩
    exact amplituhedronImage_right_mul_mem Z B ⟨C, hC, rfl⟩

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
