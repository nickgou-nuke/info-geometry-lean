import Mathlib

/-!
# Discrete square curvature on a four-point nuclear chart

This module defines the four chart points with proton and neutron coordinates in
`{15,16}`, computes their mass numbers, and proves the mixed finite-difference
formula for affine and corner-coupled scalar fields.
-/

noncomputable section

namespace NuclearChartSquareCalibration

/-- A chart point with proton coordinate `Z` and neutron coordinate `N`. -/
structure NucleusPoint where
  Z : ℕ
  N : ℕ
  deriving DecidableEq, Repr

/-- The sum of the two chart coordinates. -/
def massNumber (x : NucleusPoint) : ℕ := x.Z + x.N

/-- The square with `Z,N ∈ {15,16}`. -/
def p31s31Square :
    NucleusPoint × NucleusPoint × NucleusPoint × NucleusPoint :=
  ({ Z := 15, N := 15 },
   { Z := 16, N := 15 },
   { Z := 15, N := 16 },
   { Z := 16, N := 16 })

/-- The four coordinate sums on the explicit square are `30,31,31,32`. -/
theorem p31s31Square_mass_numbers :
    let q := p31s31Square
    massNumber q.1 = 30 ∧
    massNumber q.2.1 = 31 ∧
    massNumber q.2.2.1 = 31 ∧
    massNumber q.2.2.2 = 32 := by
  norm_num [p31s31Square, massNumber]

/-- Mixed finite difference on a scalar square. -/
def plaquetteCurvature (E00 E10 E01 E11 : ℝ) : ℝ :=
  E11 - E10 - E01 + E00

/-- An affine separable scalar field has zero mixed finite difference. -/
theorem plaquetteCurvature_affine_zero (base zSlope nSlope : ℝ) :
    plaquetteCurvature
      base
      (base + zSlope)
      (base + nSlope)
      (base + zSlope + nSlope) = 0 := by
  unfold plaquetteCurvature
  ring

/-- A corner coupling is recovered exactly by the mixed finite difference. -/
theorem plaquetteCurvature_coupled_corner
    (base zSlope nSlope coupling : ℝ) :
    plaquetteCurvature
      base
      (base + zSlope)
      (base + nSlope)
      (base + zSlope + nSlope + coupling) = coupling := by
  unfold plaquetteCurvature
  ring

/-- Consolidated chart-square arithmetic. -/
theorem nuclear_chart_square_calibration_synthesis
    (base zSlope nSlope coupling : ℝ) :
    (let q := p31s31Square;
      massNumber q.1 = 30 ∧
      massNumber q.2.1 = 31 ∧
      massNumber q.2.2.1 = 31 ∧
      massNumber q.2.2.2 = 32) ∧
    plaquetteCurvature
      base
      (base + zSlope)
      (base + nSlope)
      (base + zSlope + nSlope) = 0 ∧
    plaquetteCurvature
      base
      (base + zSlope)
      (base + nSlope)
      (base + zSlope + nSlope + coupling) = coupling :=
  ⟨p31s31Square_mass_numbers,
    plaquetteCurvature_affine_zero base zSlope nSlope,
    plaquetteCurvature_coupled_corner base zSlope nSlope coupling⟩

end NuclearChartSquareCalibration
