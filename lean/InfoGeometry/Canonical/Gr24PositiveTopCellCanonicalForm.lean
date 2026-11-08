import Mathlib
import InfoGeometry.Topology.PlabicBoundaryMeasurement
import InfoGeometry.Projective.MatrixPluckerPositiveBridge

/-!
# The positive top cell of Gr(2,4) in a fixed Plücker gauge

This module gives an explicit coordinate equivalence for the open positroid
cell with all six ordered Plücker coordinates positive, and its genuine
logarithmic top form in those positive coordinates.  It does not identify the
matrix family with a plabic graph boundary measurement, nor claim a
triangulation or a canonical form on the closed nonnegative Grassmannian.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.Gr24PositiveTopCell

open PlabicBoundaryMeasurement
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.Canonical

abbrev Matrix2x4 := Matrix (Fin 2) (Fin 4) ℝ

/-- The four positive face coordinates of the gauge `Δ₀₂ = 1`. -/
abbrev PositiveParameters := {t : Fin 4 → ℝ // ∀ i, 0 < t i}

/-- A gauge-fixed representative of the strictly positive top cell.  Columns
0 and 2 are fixed to the standard basis, so the selected Plücker coordinate
`Δ₀₂` equals one. -/
abbrev GaugeFixedTopCell :=
  {M : Matrix2x4 // M 0 0 = 1 ∧ M 1 0 = 0 ∧ M 0 2 = 0 ∧ M 1 2 = 1 ∧
    M ∈ positiveGrassmannianInterior (k := 2) (n := 4)}

/-- The standard four-coordinate chart matrix.  Its Plücker coordinates are
`(t₂, 1, t₃, t₁, t₁*t₃+t₂*t₄, t₄)` in lexicographic order. -/
def chartMatrix (t : PositiveParameters) : Matrix2x4 :=
  PlabicBoundaryMeasurement.boundaryMeasurementMatrix
    (t.1 0) (t.1 1) (t.1 2) (t.1 3)

private theorem chartMatrix_positive (t : PositiveParameters) :
    chartMatrix t ∈ positiveGrassmannianInterior (k := 2) (n := 4) := by
  apply matrixPluckerPositive_mem_positiveGrassmannianInterior
  intro i
  have ht := PlabicBoundaryMeasurement.boundaryMeasurement_totally_positive
    (t.2 0) (t.2 1) (t.2 2) (t.2 3)
  rcases ht with ⟨h01, h02, h03, h12, h13, h23⟩
  fin_cases i
  · simpa [MatrixPluckerPositive, matrixPluckerCoords_apply, chartMatrix,
      InfoGeometry.Amplituhedron.minor2,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
      using h01
  · simpa [MatrixPluckerPositive, matrixPluckerCoords_apply, chartMatrix,
      InfoGeometry.Amplituhedron.minor2,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
      using h02
  · simpa [MatrixPluckerPositive, matrixPluckerCoords_apply, chartMatrix,
      InfoGeometry.Amplituhedron.minor2,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
      using h03
  · simpa [MatrixPluckerPositive, matrixPluckerCoords_apply, chartMatrix,
      InfoGeometry.Amplituhedron.minor2,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
      using h12
  · simpa [MatrixPluckerPositive, matrixPluckerCoords_apply, chartMatrix,
      InfoGeometry.Amplituhedron.minor2, PlabicBoundaryMeasurement.boundaryMeasurementMatrix,
      mul_comm] using h13
  · simpa [MatrixPluckerPositive, matrixPluckerCoords_apply, chartMatrix,
      InfoGeometry.Amplituhedron.minor2,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix]
      using h23
/-- The positive face coordinates determine the six Plücker coordinates in
this gauge, including the Plücker relation in the `13` coordinate. -/
theorem chartMatrix_plucker_readout (t : PositiveParameters) :
    ∀ i : Fin 6, matrixPluckerCoords (chartMatrix t) i =
      match i with
      | 0 => t.1 1
      | 1 => 1
      | 2 => t.1 2
      | 3 => t.1 0
      | 4 => t.1 0 * t.1 2 + t.1 1 * t.1 3
      | 5 => t.1 3 := by
  intro i
  fin_cases i <;>
    simp [matrixPluckerCoords_apply, chartMatrix,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix] <;> ring

/-- The coordinate family lands in the gauge-fixed top cell. -/
def chartToGaugeFixedTopCell (t : PositiveParameters) : GaugeFixedTopCell := by
  refine ⟨chartMatrix t, ⟨by simp [chartMatrix, PlabicBoundaryMeasurement.boundaryMeasurementMatrix],
    by simp [chartMatrix, PlabicBoundaryMeasurement.boundaryMeasurementMatrix],
    by simp [chartMatrix, PlabicBoundaryMeasurement.boundaryMeasurementMatrix],
    by simp [chartMatrix, PlabicBoundaryMeasurement.boundaryMeasurementMatrix],
    chartMatrix_positive t⟩⟩

private theorem gaugeFixed_coordinates_positive (M : GaugeFixedTopCell) :
    ∀ i : Fin 4, 0 < (fun j : Fin 4 =>
      if j = 0 then M.1 0 1 else if j = 1 then M.1 1 1 else
      if j = 2 then M.1 1 3 else -M.1 0 3) i := by
  intro i
  have hpos := M.2.2.2.2.2
  have hpl := positiveGrassmannianInterior_mem_matrixPluckerPositive M.1 hpos
  have h00 := M.2.1
  have h10 := M.2.2.1
  have h02 := M.2.2.2.1
  have h12 := M.2.2.2.2.1
  fin_cases i
  · have h := hpl 3
    simpa [matrixPluckerCoords_apply, h00, h10, h02, h12] using h
  · have h := hpl 0
    simpa [matrixPluckerCoords_apply, h00, h10, h02, h12] using h
  · have h := hpl 2
    simpa [matrixPluckerCoords_apply, h00, h10, h02, h12] using h
  · have h := hpl 5
    simpa [matrixPluckerCoords_apply, h00, h10, h02, h12] using h

/-- Recover the four positive coordinates from the gauge-fixed matrix. -/
def gaugeFixedCoordinates (M : GaugeFixedTopCell) : PositiveParameters :=
  ⟨(fun j : Fin 4 =>
      if j = 0 then M.1 0 1 else if j = 1 then M.1 1 1 else
      if j = 2 then M.1 1 3 else -M.1 0 3),
    gaugeFixed_coordinates_positive M⟩

theorem chartToGaugeFixedTopCell_left_inv (t : PositiveParameters) :
    gaugeFixedCoordinates (chartToGaugeFixedTopCell t) = t := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [gaugeFixedCoordinates, chartToGaugeFixedTopCell,
    chartMatrix,
    PlabicBoundaryMeasurement.boundaryMeasurementMatrix]

theorem chartToGaugeFixedTopCell_right_inv (M : GaugeFixedTopCell) :
    chartToGaugeFixedTopCell (gaugeFixedCoordinates M) = M := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartToGaugeFixedTopCell, chartMatrix, gaugeFixedCoordinates,
      PlabicBoundaryMeasurement.boundaryMeasurementMatrix,
      M.2.1, M.2.2.1, M.2.2.2.1, M.2.2.2.2]

/-- The positive orthant is exactly the gauge-fixed representative of the
strictly positive top positroid cell. -/
def topCellCoordinateEquiv : PositiveParameters ≃ GaugeFixedTopCell where
  toFun := chartToGaugeFixedTopCell
  invFun := gaugeFixedCoordinates
  left_inv := chartToGaugeFixedTopCell_left_inv
  right_inv := chartToGaugeFixedTopCell_right_inv

/-- The top-cell logarithmic density in positive coordinates. -/
noncomputable def dlogDensity (t : PositiveParameters) : ℝ :=
  ∏ i : Fin 4, (t.1 i)⁻¹

/-- The oriented coordinate frame on the four-dimensional parameter space. -/
def coordinateFrame : Fin 4 → (Fin 4 → ℝ) :=
  fun i => Pi.single i 1

/-- The top-cell canonical form, expressed as the coefficient of
`dlog t₀ ∧ dlog t₁ ∧ dlog t₂ ∧ dlog t₃` against the standard orientation. -/
noncomputable def canonicalTopForm (t : PositiveParameters) :
    ((Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ) :=
  dlogDensity t • (Pi.basisFun ℝ (Fin 4)).det

theorem canonicalTopForm_coordinateFrame (t : PositiveParameters) :
    canonicalTopForm t coordinateFrame = dlogDensity t := by
  have hframe : coordinateFrame = Pi.basisFun ℝ (Fin 4) := by
    funext i
    simp [coordinateFrame, Pi.basisFun_apply]
  rw [canonicalTopForm, hframe]
  change dlogDensity t * (Pi.basisFun ℝ (Fin 4)).det
    (Pi.basisFun ℝ (Fin 4)) = dlogDensity t
  rw [Module.Basis.det_self]
  simp

/-- The coefficient of the logarithmic boundary residue obtained by removing
coordinate `i` from the dlog product. -/
noncomputable def boundaryResidueDensity (t : PositiveParameters) (i : Fin 4) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (t.1 j)⁻¹

theorem dlogDensity_factor_boundary_coordinate (t : PositiveParameters) (i : Fin 4) :
    dlogDensity t = (t.1 i)⁻¹ * boundaryResidueDensity t i := by
  rw [dlogDensity, boundaryResidueDensity]
  simpa using (Finset.mul_prod_erase Finset.univ (fun j : Fin 4 => (t.1 j)⁻¹)
    (Finset.mem_univ i)).symm

/-- The logarithmic residue coefficient of the top-cell form at the coordinate
boundary `tᵢ = 0` is the product of the remaining three logarithmic factors.
The identity is stated after evaluation on the chosen oriented frame, so it
does not hide a differential-form convention in a scalar abbreviation. -/
theorem canonicalTopForm_log_residue (t : PositiveParameters) (i : Fin 4) :
    t.1 i * canonicalTopForm t coordinateFrame = boundaryResidueDensity t i := by
  rw [canonicalTopForm_coordinateFrame, dlogDensity_factor_boundary_coordinate]
  have hpos : 0 < t.1 i := t.2 i
  calc
    t.1 i * ((t.1 i)⁻¹ * boundaryResidueDensity t i) =
        (t.1 i * (t.1 i)⁻¹) * boundaryResidueDensity t i := by ring
    _ = boundaryResidueDensity t i := by
      rw [mul_inv_cancel₀ (ne_of_gt hpos), one_mul]

/-- The residue coefficient is positive throughout the positive boundary
chart, as required for the oriented logarithmic form. -/
theorem boundaryResidueDensity_pos (t : PositiveParameters) (i : Fin 4) :
    0 < boundaryResidueDensity t i := by
  unfold boundaryResidueDensity
  apply Finset.prod_pos
  intro j hj
  exact inv_pos.mpr (t.2 j)

theorem dlogDensity_pos (t : PositiveParameters) : 0 < dlogDensity t := by
  apply Finset.prod_pos
  intro i hi
  exact inv_pos.mpr (t.2 i)

end InfoGeometry.Canonical.Gr24PositiveTopCell
