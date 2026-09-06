import Mathlib.Tactic

/-!
# Discrete square curvature on a four-point nuclear chart

This module defines the four chart points with proton and neutron coordinates in
`{15,16}`, computes their mass numbers, and proves the mixed finite-difference
formula for affine and corner-coupled scalar fields.
-/

noncomputable section

namespace NuclearChartSquareCalibration

/-- A chart point with proton coordinate `Z` and neutron coordinate `N`. -/
abbrev NucleusPoint := ℕ × ℕ

namespace NucleusPoint

abbrev Z (x : NucleusPoint) : ℕ := x.1

abbrev N (x : NucleusPoint) : ℕ := x.2

end NucleusPoint

/-- The sum of the two chart coordinates. -/
def massNumber (x : NucleusPoint) : ℕ := x.Z + x.N

/-- The square with `Z,N ∈ {15,16}`. -/
def p31s31Square :
    NucleusPoint × NucleusPoint × NucleusPoint × NucleusPoint :=
  ((15, 15),
   (16, 15),
   (15, 16),
   (16, 16))

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

end NuclearChartSquareCalibration
