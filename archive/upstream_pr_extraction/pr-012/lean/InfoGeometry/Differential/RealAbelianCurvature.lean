/-
InfoGeometry/Differential/RealAbelianCurvature.lean

Pure real abelian curvature and scalar-first Bochner integration.
No complex imports.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.Basic
import InfoGeometry.Geometry.RealUpperHalfPlane

noncomputable section

namespace InfoGeometry.Differential

open MeasureTheory
open InfoGeometry.Geometry

/-- Truncation heights for the real modular fundamental domain. -/
abbrev TruncHeight : Type :=
  ℝ

namespace TruncHeight

/-- Convert a real limit parameter into a cutoff height. -/
def fromReal (Y : ℝ) : TruncHeight :=
  Y ^ 2 + 1

/-- The cutoff height obtained from `Y` is always at least `1`. -/
theorem one_le_fromReal (Y : ℝ) : 1 ≤ fromReal Y := by
  dsimp [fromReal]
  nlinarith [sq_nonneg Y]

end TruncHeight

/--
The real truncated fundamental domain as a subset of the ambient real plane.

The condition `0 < p.2` is retained in the set definition, so the integrand
can reconstruct a point of `RUpperHalfPlane` without any hidden complex model.
-/
def realTruncatedFDPlane (Y : TruncHeight) : Set (ℝ × ℝ) :=
  { p |
    -(1 : ℝ) / 2 ≤ p.1 ∧
    p.1 ≤ (1 : ℝ) / 2 ∧
    1 ≤ p.1 ^ 2 + p.2 ^ 2 ∧
    0 < p.2 ∧
    p.2 ≤ Y }

/-- Hyperbolic density `dx dy / y²`, expressed as a real scalar. -/
def hyperbolicDensity (τ : RealUpperHalfPlane) : ℝ :=
  1 / τ.y ^ 2

/-- Scalar coefficient of the abelian curvature two-form. -/
abbrev RealScalarCurvatureDensity : Type :=
  RealUpperHalfPlane → ℝ

/-- Curvature density multiplied by the hyperbolic area density. -/
def bulkDensity (F : RealScalarCurvatureDensity) (τ : RealUpperHalfPlane) : ℝ :=
  F τ * hyperbolicDensity τ

/--
A total integrand on `ℝ × ℝ`.

Outside the upper half-plane it is defined as `0`; on the truncated domain,
the `if` branch uses the proof `0 < p.2`.
-/
def bulkDensityOnPlane
    (F : RealScalarCurvatureDensity)
    (p : ℝ × ℝ) : ℝ :=
  if hp : 0 < p.2 then
    bulkDensity F ⟨p.1, p.2, hp⟩
  else
    0

variable {Bivector : Type*}
  [NormedAddCommGroup Bivector]
  [NormedSpace ℝ Bivector]

/--
The scalar real bulk curvature integral over the truncated domain.
-/
def realBulkCurvatureScalar
    (F : RealScalarCurvatureDensity)
    (Y : TruncHeight) : ℝ :=
  ∫ p in realTruncatedFDPlane Y, bulkDensityOnPlane F p

/-- Push the scalar curvature integral into the fixed real bivector line. -/
def realBulkCurvatureIntegral
    (basisMap : ℝ →L[ℝ] Bivector)
    (F : RealScalarCurvatureDensity)
    (Y : TruncHeight) : Bivector :=
  basisMap (realBulkCurvatureScalar F Y)

/-- A cutoff map from a real parameter to a valid truncation height. -/
def cutoff (Y : ℝ) : TruncHeight :=
  TruncHeight.fromReal Y

/-- Bulk curvature integral along the real cutoff path `Y ↦ Y² + 1`. -/
noncomputable def realBulkCurvatureIntegralAt
    (basisMap : ℝ →L[ℝ] Bivector)
    (F : RealScalarCurvatureDensity)
    (Y : ℝ) : Bivector :=
  realBulkCurvatureIntegral basisMap F (cutoff Y)

/--
Variant for a density already expressed relative to Euclidean coordinate area
`dx dy`, with no hyperbolic weighting.
-/
noncomputable def realBulkCurvatureIntegralEuclidean
    (basisMap : ℝ →L[ℝ] Bivector)
    (F : RealScalarCurvatureDensity)
    (Y : TruncHeight) : Bivector :=
  basisMap
    (∫ p in realTruncatedFDPlane Y,
      bulkDensityOnPlane F p)

end InfoGeometry.Differential
