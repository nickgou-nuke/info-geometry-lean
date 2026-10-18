/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PositiveGrassmannianAmplituhedron
import InfoGeometry.Canonical.PositiveGrassmannianBCFWCells

/-!
# External-data convention bridge for finite positive-Grassmannian charts

The canonical chart writes external data as an `n × m` matrix and maps `C`
to `C * Z`.  The BCFW-cell chart stores the transpose, with shape
`(k + m) × n`, and maps `C` to `C * Zᵀ`.  This file proves these are the same
finite matrix construction after transposing the external-data layout. Here
“orientation” in the module name means matrix storage convention only; no
Plücker sign change, quotient orientation, or oriented positive geometry is
defined or compared.
It does not construct a Grassmannian quotient, canonical differential form,
or scattering-amplitude theorem.
-/

namespace InfoGeometry.Topology.PositiveGrassmannianAmplituhedronOrientationBridge

open InfoGeometry.Canonical
open Matrix

variable {k n m : ℕ}

/-- The two owners encode the same ordered maximal minors: one through a
submatrix determinant, the other through its row/column function. -/
theorem totallyNonnegative_iff_mem_positiveGrassmannianChart
    (C : Matrix (Fin k) (Fin n) ℝ) :
    InfoGeometry.Canonical.IsTotallyNonnegative C ↔
      C ∈ InfoGeometry.Canonical.positiveGrassmannianChart := by
  change InfoGeometry.Canonical.IsTotallyNonnegative C ↔
    InfoGeometry.Canonical.HasNonnegativeMaximalMinors C
  constructor
  · intro h I hI
    have hminor : InfoGeometry.Canonical.extractMinor C I =
        InfoGeometry.Canonical.maximalMinor C I := rfl
    have hI' := h I hI
    change 0 ≤ InfoGeometry.Canonical.extractMinor C I at hI'
    change 0 ≤ InfoGeometry.Canonical.maximalMinor C I
    rw [← hminor]
    exact hI'
  · intro h I hI
    have hminor : InfoGeometry.Canonical.extractMinor C I =
        InfoGeometry.Canonical.maximalMinor C I := rfl
    have hI' := h I hI
    change 0 ≤ InfoGeometry.Canonical.maximalMinor C I at hI'
    change 0 ≤ InfoGeometry.Canonical.extractMinor C I
    rw [hminor]
    exact hI'

/-- The two owners define equal finite amplituhedron images once their
external-data orientation is aligned. -/
theorem treeAmplituhedron_eq_amplituhedronImage_transpose
    (Z : Matrix (Fin (k + m)) (Fin n) ℝ) :
    InfoGeometry.Canonical.TreeAmplituhedron Z =
      InfoGeometry.Canonical.amplituhedronImage Zᵀ := by
  ext Y
  constructor
  · rintro ⟨C, hC, rfl⟩
    refine ⟨C, ?_, rfl⟩
    exact (totallyNonnegative_iff_mem_positiveGrassmannianChart C).mp hC
  · rintro ⟨C, hC, hY⟩
    refine ⟨C, ?_, ?_⟩
    · exact (totallyNonnegative_iff_mem_positiveGrassmannianChart C).mpr hC
    · simpa [InfoGeometry.Canonical.bcfwCellMap,
        InfoGeometry.Canonical.amplituhedronMap] using hY.symm

/-- Images of any specified representative cell agree across the same two
external-data orientations. -/
theorem cellImage_eq_image_transpose
    (Z : Matrix (Fin (k + m)) (Fin n) ℝ)
    (cell : Set (Matrix (Fin k) (Fin n) ℝ)) :
    InfoGeometry.Canonical.cellImage Z cell =
      InfoGeometry.Canonical.amplituhedronMap Zᵀ '' cell := by
  ext Y
  constructor
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C, hC, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C, hC, rfl⟩

end InfoGeometry.Topology.PositiveGrassmannianAmplituhedronOrientationBridge
