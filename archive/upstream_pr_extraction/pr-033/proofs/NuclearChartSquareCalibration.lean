import proofs.MirrorValencePairCalibration

/-!
# Nuclear-chart square calibration

This file extends the mirror-pair calibration to an axis-aligned plaquette in
the nuclear chart.  Around the `31P/31S` mirror pair, the natural square is

```text
      N=16      31P ---- 32S
                 |        |
      N=15      30P ---- 31S
                Z=15    Z=16
```

The finite invariant is the discrete plaquette curvature
`E₁₁ - E₁₀ - E₀₁ + E₀₀`.  It vanishes for a separable affine
proton/neutron field and measures the residual proton-neutron square coupling
in the executable calibration script.
-/

noncomputable section

namespace NuclearChartSquareCalibration

/-- Nuclear-chart point with proton number `Z` and neutron number `N`. -/
structure NucleusPoint where
  Z : ℕ
  N : ℕ
  deriving Repr

/-- Mass number. -/
def massNumber (x : NucleusPoint) : ℕ :=
  x.Z + x.N

/-- The `Z,N ∈ {15,16}` square around the `31P/31S` mirror pair. -/
def p31s31Square : NucleusPoint × NucleusPoint × NucleusPoint × NucleusPoint :=
  ({ Z := 15, N := 15 },
   { Z := 16, N := 15 },
   { Z := 15, N := 16 },
   { Z := 16, N := 16 })

theorem p31s31Square_mass_numbers :
    let q := p31s31Square
    massNumber q.1 = 30 ∧
    massNumber q.2.1 = 31 ∧
    massNumber q.2.2.1 = 31 ∧
    massNumber q.2.2.2 = 32 := by
  unfold p31s31Square massNumber
  norm_num

/-- Discrete square curvature for energies at `(0,0),(1,0),(0,1),(1,1)`. -/
def plaquetteCurvature (E00 E10 E01 E11 : ℝ) : ℝ :=
  E11 - E10 - E01 + E00

/-- An affine separable field has zero square curvature. -/
theorem plaquetteCurvature_affine_zero (base zSlope nSlope : ℝ) :
    plaquetteCurvature
      base
      (base + zSlope)
      (base + nSlope)
      (base + zSlope + nSlope) = 0 := by
  unfold plaquetteCurvature
  ring

/-- Square coupling is exactly the curvature added at the northeast corner. -/
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

end noncomputable section
