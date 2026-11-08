/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.PlabicBoundaryMeasurement
import InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
import InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon

/-!
# Boundary chart / Postnikov channel bridge

## i. Overview
This module transports the existing Postnikov `Gr(2,4)` boundary-channel
decomposition to `PlabicBoundaryMeasurement`'s `minor2` API. The two source
owners use the same explicit four-parameter matrix. This is a matrix-chart
comparison; it does not construct a planar graph or prove a local graph
square-move boundary-measurement theorem.

## ii. Key results
- `boundaryMeasurementMatrix_eq_postnikovTop24`
- `boundary_measurement_postnikov_channels_and_dag_readout`
- `boundary_chart_plucker_coordinates_match_zorn_ray`
- `boundary_chart_zorn_ray_is_klein_null`
- `positive_boundary_chart_ray_surprise_without_self_foam`
- `boundary_chart_all_minors_as_two_ray_scattering_foam`

## iii. Table of contents
- Postnikov channel decomposition and DAG readout
- Chart Plücker coordinates and Klein-quadric nilpotency
- Six-minor reference bracket and two-ray Zorn scattering foam

## iv. References
- Alexander Postnikov, *Total positivity, Grassmannians, and networks* (2006)
- `InfoGeometry.Topology.PlabicBoundaryMeasurement`
- `InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon`

#### BUCKET 1 — Proved Kernel Content
- `boundaryMeasurementMatrix_eq_postnikovTop24`
- `boundary_measurement_postnikov_channels_and_dag_readout`
- `boundary_chart_plucker_coordinates_match_zorn_ray`
- `boundary_chart_zorn_ray_is_klein_null`
- `positive_boundary_chart_ray_surprise_without_self_foam`
- `boundary_chart_all_minors_as_two_ray_scattering_foam`

#### BUCKET 2 — Conditional / Interface Boundaries
- `positive_boundary_chart_ray_surprise_without_self_foam` holds under positivity hypotheses on the chart parameters.

#### BUCKET 3 — Open / Unformalized
- General arbitrary-rank plabic network reductions remain outside this `Gr(2,4)` chart comparison.
-/

namespace InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge

open PlabicBoundaryMeasurement
open InfoGeometry.Amplituhedron
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset

open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon

/-- The boundary-measurement chart and the Postnikov top-cell chart are
definitionally the same `2 × 4` matrix after identifying parameters. -/
theorem boundaryMeasurementMatrix_eq_postnikovTop24
    (t₁ t₂ t₃ t₄ : ℝ) :
    boundaryMeasurementMatrix t₁ t₂ t₃ t₄ =
      plabicPositroidTop24 t₁ t₂ t₃ t₄ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PlabicBoundaryMeasurement.boundaryMeasurementMatrix,
      plabicPositroidTop24]

/-- The `2 × 2` minor `minor2 C i j` coincides with the Postnikov minor `pluckerMinor24 C i j`. -/
private theorem minor2_eq_postnikovMinor
    (C : Matrix (Fin 2) (Fin 4) ℝ) (i j : Fin 4) :
    minor2 C i j = pluckerMinor24 C i j := by
  simp only [InfoGeometry.Amplituhedron.minor2, pluckerMinor24]
  ring

/-- The Postnikov two-channel boundary decomposition, transported to the
boundary-measurement chart: `Δ₁₃` is the sum of the `w₁w₃` and `w₂w₄`
boundary contributions. The final conjunct spells out those two terms through
the chart-to-DAG route readout, tying this decomposition to the finite
terminating path model proved in the chart owner. -/
theorem boundary_measurement_postnikov_channels_and_dag_readout
    (t₁ t₂ t₃ t₄ : ℝ) :
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 =
      minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ 0) 1 3 +
        minor2 (boundaryMeasurementMatrix 0 t₂ t₃ t₄) 1 3 ∧
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ 0) 1 3 = t₁ * t₃ ∧
    minor2 (boundaryMeasurementMatrix 0 t₂ t₃ t₄) 1 3 = t₂ * t₄ ∧
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 =
      chartTwoRouteGreen t₁ t₂ t₃ t₄ 0 2 ∧
    minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 =
      chartDiamondGreen t₁ t₂ t₃ t₄ 0 3 := by
  have hPost :=
    postnikov_urbanRenewal_mutation_and_bcfw_st_channels
      1 1 1 t₁ t₂ t₃ t₄
  have hSplit := hPost.2.2.1
  have hMinor (a b c d : ℝ) :
      minor2 (boundaryMeasurementMatrix a b c d) 1 3 =
        pluckerMinor24 (plabicPositroidTop24 a b c d) 1 3 := by
    rw [boundaryMeasurementMatrix_eq_postnikovTop24]
    exact minor2_eq_postnikovMinor _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hMinor t₁ t₂ t₃ t₄, hMinor t₁ t₂ t₃ 0,
      hMinor 0 t₂ t₃ t₄]
    exact hSplit
  · rw [PlabicBoundaryMeasurement.plucker_13]
    ring
  · rw [PlabicBoundaryMeasurement.plucker_13]
    ring
  · exact boundaryMeasurement_plucker_13_eq_two_route_readout
      t₁ t₂ t₃ t₄
  · exact boundaryMeasurement_plucker_13_eq_diamond_readout
      t₁ t₂ t₃ t₄

/-- First row of the positive `Gr(2,4)` chart regarded as a twistor in `ℝ⁴`. -/
def chartTwistor0 (t₁ t₄ : ℝ) : Twistor4 ℝ :=
  ⟨1, t₁, 0, -t₄⟩

/-- Second row of the positive `Gr(2,4)` chart regarded as a twistor in `ℝ⁴`. -/
def chartTwistor1 (t₂ t₃ : ℝ) : Twistor4 ℝ :=
  ⟨0, t₂, 1, t₃⟩

/-- Third standard coordinate basis twistor `(0, 0, 1, 0)` in `ℝ⁴`. -/
def referenceTwistor2 : Twistor4 ℝ := ⟨0, 0, 1, 0⟩

/-- Fourth standard coordinate basis twistor `(0, 0, 0, 1)` in `ℝ⁴`. -/
def referenceTwistor3 : Twistor4 ℝ := ⟨0, 0, 0, 1⟩

/-- First standard coordinate basis twistor `(1, 0, 0, 0)` in `ℝ⁴`. -/
def referenceTwistor0 : Twistor4 ℝ := ⟨1, 0, 0, 0⟩

/-- Second standard coordinate basis twistor `(0, 1, 0, 0)` in `ℝ⁴`. -/
def referenceTwistor1 : Twistor4 ℝ := ⟨0, 1, 0, 0⟩

/-- The chart's six ordered maximal minors are exactly its row-pair Plücker
coordinates in the Zorn owner's electric/magnetic splitting:
`u = (Δ₀₁, Δ₀₂, Δ₀₃)` and `v = (Δ₂₃, -Δ₁₃, Δ₁₂)`. -/
theorem boundary_chart_plucker_coordinates_match_zorn_ray
    (t₁ t₂ t₃ t₄ : ℝ) :
    Twistor4.pluckerU (chartTwistor0 t₁ t₄)
        (chartTwistor1 t₂ t₃) =
      ⟨minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1,
       minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 2,
       minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3⟩ ∧
    Twistor4.pluckerV (chartTwistor0 t₁ t₄)
        (chartTwistor1 t₂ t₃) =
      ⟨minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 2 3,
       -minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3,
       minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2⟩ := by
  constructor
  · rw [PlabicBoundaryMeasurement.plucker_01,
      PlabicBoundaryMeasurement.plucker_02,
      PlabicBoundaryMeasurement.plucker_03]
    ext <;> simp [chartTwistor0, chartTwistor1, Twistor4.pluckerU]
  · rw [PlabicBoundaryMeasurement.plucker_23,
      PlabicBoundaryMeasurement.plucker_13,
      PlabicBoundaryMeasurement.plucker_12]
    ext <;> (simp [chartTwistor0, chartTwistor1, Twistor4.pluckerV,
      Twistor4.spatialVec, Vec3.cross] <;> ring)

/-- A chart point determines a simple twistor ray on the Klein quadric; hence
its associated Zorn ray is square-zero. This makes the Grassmannian chart to
Klein/Zorn map explicit at the carrier and coordinate level. -/
theorem boundary_chart_zorn_ray_is_klein_null
    (t₁ t₂ t₃ t₄ : ℝ) :
    Vec3.dot
        (Twistor4.pluckerU (chartTwistor0 t₁ t₄)
          (chartTwistor1 t₂ t₃))
        (Twistor4.pluckerV (chartTwistor0 t₁ t₄)
          (chartTwistor1 t₂ t₃)) = 0 ∧
    zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) *
      zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) = 0 := by
  have hKlein := klein_quadric_and_zorn_nilpotency_of_twistor_lines
    (0 : Vec3 ℝ) (0 : Vec3 ℝ)
    (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
  exact ⟨hKlein.2.2.1, hKlein.2.2.2⟩

/-- In the strictly positive chart, the two-channel minor `Δ₁₃ = t₁ t₃ + t₂ t₄` is
strictly positive and both halves of the Plücker vector are nonzero even though the
associated simple-ray Zorn operator remains square-zero. This is a concrete chart-level
instance of surprise without self-foam. -/
theorem positive_boundary_chart_ray_surprise_without_self_foam
    (t₁ t₂ t₃ t₄ : ℝ)
    (h₁ : 0 < t₁) (h₂ : 0 < t₂) (h₃ : 0 < t₃) (h₄ : 0 < t₄) :
    0 < minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 ∧
    Twistor4.pluckerU (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) ≠ 0 ∧
    Twistor4.pluckerV (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) ≠ 0 ∧
    zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) *
      zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) = 0 := by
  have h13 : 0 < minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 := by
    rw [PlabicBoundaryMeasurement.plucker_13]
    nlinarith
  have hU : Twistor4.pluckerU (chartTwistor0 t₁ t₄)
      (chartTwistor1 t₂ t₃) ≠ 0 := by
    intro h
    have hy := congrArg Vec3.y h
    simp [Twistor4.pluckerU, chartTwistor0, chartTwistor1] at hy
  have hV : Twistor4.pluckerV (chartTwistor0 t₁ t₄)
      (chartTwistor1 t₂ t₃) ≠ 0 := by
    intro h
    have hx := congrArg Vec3.x h
    simp [Twistor4.pluckerV, Twistor4.spatialVec, chartTwistor0,
      chartTwistor1, Vec3.cross] at hx
    linarith
  exact ⟨h13, hU, hV,
    (boundary_chart_zorn_ray_is_klein_null t₁ t₂ t₃ t₄).2⟩

/-- The chart minor `Δ₀₁` is a four-twistor bracket with the complementary
coordinate ray, and therefore is exactly the scalar in the corresponding
two-ray Zorn scattering square. For positive `t₂`, this chart/reference-ray
scattering survives although the chart ray alone is square-zero. -/
theorem boundary_chart_minor_as_two_ray_scattering_foam
    (t₁ t₂ t₃ t₄ : ℝ) :
    twistorBracket4 (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
      referenceTwistor2 referenceTwistor3 =
        minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1 ∧
    (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
      zornPlucker referenceTwistor2 referenceTwistor3) *
      (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
        zornPlucker referenceTwistor2 referenceTwistor3) =
      ZornMatrix.smul
        (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1)
        (1 : ZornMatrix ℝ) := by
  have hBracket :
      twistorBracket4 (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
        referenceTwistor2 referenceTwistor3 =
          minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1 := by
    rw [PlabicBoundaryMeasurement.plucker_01]
    simp [twistorBracket4, Archetypes.TwistorAmplituhedronZornBaryon.det4, ofTwistors,
      chartTwistor0, chartTwistor1, referenceTwistor2, referenceTwistor3]
  refine ⟨hBracket, ?_⟩
  rw [two_ray_plucker_sum_square_eq_four_bracket, hBracket]

/-- The chart's first minor supplies a nonzero scattering bracket whenever
`t₂` is positive. Together with `positive_boundary_chart_ray_surprise_without_self_foam`,
this gives a positive chart example whose individual ray is square-zero but
whose pairing with a complementary reference ray has nonzero bracket. -/
theorem positive_boundary_chart_reference_bracket_survives
    (t₁ t₂ t₃ t₄ : ℝ) (h₂ : 0 < t₂) :
    twistorBracket4 (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
      referenceTwistor2 referenceTwistor3 ≠ 0 := by
  rw [(boundary_chart_minor_as_two_ray_scattering_foam t₁ t₂ t₃ t₄).1,
    PlabicBoundaryMeasurement.plucker_01]
  exact ne_of_gt h₂

/-- All six Plücker coordinates of the chart are four-twistor brackets with
the complementary pair of coordinate twistors. Their two-ray Zorn squares
therefore recover every chart minor through the general bracket-square
theorem `two_ray_plucker_sum_square_eq_four_bracket`. -/
theorem boundary_chart_all_minors_as_reference_brackets
    (t₁ t₂ t₃ t₄ : ℝ) :
    twistorBracket4 (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
      referenceTwistor2 referenceTwistor3 =
        minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1 ∧
    twistorBracket4 (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
      referenceTwistor3 referenceTwistor1 =
        minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 2 ∧
    twistorBracket4 (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
      referenceTwistor1 referenceTwistor2 =
        minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3 ∧
    twistorBracket4 (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
      referenceTwistor0 referenceTwistor3 =
        minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2 ∧
    twistorBracket4 (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
      referenceTwistor2 referenceTwistor0 =
        minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3 ∧
    twistorBracket4 (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃)
      referenceTwistor0 referenceTwistor1 =
        minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 2 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PlabicBoundaryMeasurement.plucker_01]
    simp [twistorBracket4, Archetypes.TwistorAmplituhedronZornBaryon.det4, ofTwistors, chartTwistor0, chartTwistor1,
      referenceTwistor2, referenceTwistor3]
  · rw [PlabicBoundaryMeasurement.plucker_02]
    simp [twistorBracket4, Archetypes.TwistorAmplituhedronZornBaryon.det4, ofTwistors, chartTwistor0, chartTwistor1,
      referenceTwistor1, referenceTwistor3]
  · rw [PlabicBoundaryMeasurement.plucker_03]
    simp [twistorBracket4, Archetypes.TwistorAmplituhedronZornBaryon.det4, ofTwistors, chartTwistor0, chartTwistor1,
      referenceTwistor1, referenceTwistor2]
  · rw [PlabicBoundaryMeasurement.plucker_12]
    simp [twistorBracket4, Archetypes.TwistorAmplituhedronZornBaryon.det4, ofTwistors, chartTwistor0, chartTwistor1,
      referenceTwistor0, referenceTwistor3]
  · rw [PlabicBoundaryMeasurement.plucker_13]
    simp [twistorBracket4, Archetypes.TwistorAmplituhedronZornBaryon.det4, ofTwistors, chartTwistor0, chartTwistor1,
      referenceTwistor0, referenceTwistor2]
    ring
  · rw [PlabicBoundaryMeasurement.plucker_23]
    simp [twistorBracket4, Archetypes.TwistorAmplituhedronZornBaryon.det4, ofTwistors, chartTwistor0, chartTwistor1,
      referenceTwistor0, referenceTwistor1]

/-- Each of the six chart minors is also realized as the scalar of a two-ray
Zorn scattering square, pairing the chart ray with the complementary
coordinate ray used in `boundary_chart_all_minors_as_reference_brackets`.
This is an algebraic bracket realization; the reference rays are not asserted
to be edges of a plabic graph. -/
theorem boundary_chart_all_minors_as_two_ray_scattering_foam
    (t₁ t₂ t₃ t₄ : ℝ) :
    (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
      zornPlucker referenceTwistor2 referenceTwistor3) *
      (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
        zornPlucker referenceTwistor2 referenceTwistor3) =
      ZornMatrix.smul (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 1)
        (1 : ZornMatrix ℝ) ∧
    (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
      zornPlucker referenceTwistor3 referenceTwistor1) *
      (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
        zornPlucker referenceTwistor3 referenceTwistor1) =
      ZornMatrix.smul (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 2)
        (1 : ZornMatrix ℝ) ∧
    (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
      zornPlucker referenceTwistor1 referenceTwistor2) *
      (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
        zornPlucker referenceTwistor1 referenceTwistor2) =
      ZornMatrix.smul (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 0 3)
        (1 : ZornMatrix ℝ) ∧
    (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
      zornPlucker referenceTwistor0 referenceTwistor3) *
      (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
        zornPlucker referenceTwistor0 referenceTwistor3) =
      ZornMatrix.smul (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 2)
        (1 : ZornMatrix ℝ) ∧
    (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
      zornPlucker referenceTwistor2 referenceTwistor0) *
      (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
        zornPlucker referenceTwistor2 referenceTwistor0) =
      ZornMatrix.smul (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3)
        (1 : ZornMatrix ℝ) ∧
    (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
      zornPlucker referenceTwistor0 referenceTwistor1) *
      (zornPlucker (chartTwistor0 t₁ t₄) (chartTwistor1 t₂ t₃) +
        zornPlucker referenceTwistor0 referenceTwistor1) =
      ZornMatrix.smul (minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 2 3)
        (1 : ZornMatrix ℝ) := by
  have h := boundary_chart_all_minors_as_reference_brackets t₁ t₂ t₃ t₄
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [two_ray_plucker_sum_square_eq_four_bracket, h.1]
  · rw [two_ray_plucker_sum_square_eq_four_bracket, h.2.1]
  · rw [two_ray_plucker_sum_square_eq_four_bracket, h.2.2.1]
  · rw [two_ray_plucker_sum_square_eq_four_bracket, h.2.2.2.1]
  · rw [two_ray_plucker_sum_square_eq_four_bracket, h.2.2.2.2.1]
  · rw [two_ray_plucker_sum_square_eq_four_bracket, h.2.2.2.2.2]

end InfoGeometry.Canonical.PlabicBoundaryPostnikovBridge
