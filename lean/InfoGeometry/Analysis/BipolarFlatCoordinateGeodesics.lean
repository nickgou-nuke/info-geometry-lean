import InfoGeometry.Analysis.BipolarOrthogonalFlowSplit
import Mathlib.Tactic

/-!
# Flat affine geodesics in bipolar logarithmic coordinates

The pullback metric associated with a local logarithmic chart is Euclidean in
coordinates `(η, θ)`: `dη² + dθ²`.  This file formalizes the safe finite affine
content of that statement.

A curve in the coordinate carrier is declared flat-affine when its centered
second difference vanishes.  Every curve `p + t v` has this property.  In
particular:

* the negative-`η` coordinate line keeps `θ` fixed;
* the `θ` coordinate line keeps `η` fixed;
* both have unit coordinate speed and orthogonal velocities.

These are the coordinate representatives of the local geodesics in a flat
`(η,θ)` chart.  No global Riemannian manifold, Levi-Civita connection, or claim
about Euclidean field lines in the original `s`-plane is introduced here.

The general identity
`∇_{grad f} grad f = (1/2) grad ‖grad f‖²`
requires the full gradient of the squared norm to vanish along a geodesic; mere
constancy of the norm in the flow direction is not used as an equivalence.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics

open InfoGeometry.Analysis.BipolarPlanarHodgePair
open InfoGeometry.Analysis.BipolarOrthogonalFlowSplit

/-- Point/tangent carrier for the flat logarithmic coordinate plane. -/
abbrev FlatCoordinatePoint := PlaneCovector

/-- Unit coordinate vector in the `η` direction. -/
def etaBasis : FlatCoordinatePoint := ![1, 0]

/-- Unit coordinate vector in the `θ` direction. -/
def thetaBasis : FlatCoordinatePoint := ![0, 1]

/-- Flat affine line with initial point `p` and constant velocity `v`. -/
def affineCoordinateLine
    (p v : FlatCoordinatePoint) (t : ℝ) : FlatCoordinatePoint :=
  p + t • v

/-- Centered second difference of a coordinate curve. -/
def centeredSecondDifference
    (γ : ℝ → FlatCoordinatePoint) (t h : ℝ) : FlatCoordinatePoint :=
  γ (t + h) - (2 : ℝ) • γ t + γ (t - h)

/-- Finite affine-geodesic predicate for the flat coordinate carrier. -/
def IsFlatAffineGeodesic (γ : ℝ → FlatCoordinatePoint) : Prop :=
  ∀ t h, centeredSecondDifference γ t h = 0

/-- Every constant-velocity affine line has zero centered second difference. -/
theorem affineCoordinateLine_isFlatAffineGeodesic
    (p v : FlatCoordinatePoint) :
    IsFlatAffineGeodesic (affineCoordinateLine p v) := by
  intro t h
  ext i
  fin_cases i <;>
    simp [centeredSecondDifference, affineCoordinateLine] <;>
    ring

/-- Exact increment law for an affine coordinate line. -/
theorem affineCoordinateLine_increment
    (p v : FlatCoordinatePoint) (t h : ℝ) :
    affineCoordinateLine p v (t + h) - affineCoordinateLine p v t = h • v := by
  ext i
  fin_cases i <;> simp [affineCoordinateLine] <;> ring

/-- Barycentric affine-line identity. -/
theorem affineCoordinateLine_barycentric
    (p v : FlatCoordinatePoint) (a t u : ℝ) :
    affineCoordinateLine p v ((1 - a) * t + a * u) =
      (1 - a) • affineCoordinateLine p v t +
        a • affineCoordinateLine p v u := by
  ext i
  fin_cases i <;> simp [affineCoordinateLine] <;> ring

/-- Coordinate line following the negative `η` gradient direction. -/
def negativeEtaLine (p : FlatCoordinatePoint) (t : ℝ) : FlatCoordinatePoint :=
  affineCoordinateLine p (-etaBasis) t

/-- Coordinate line following the positive `θ` direction. -/
def thetaLine (p : FlatCoordinatePoint) (t : ℝ) : FlatCoordinatePoint :=
  affineCoordinateLine p thetaBasis t

@[simp] theorem negativeEtaLine_eta (p : FlatCoordinatePoint) (t : ℝ) :
    negativeEtaLine p t 0 = p 0 - t := by
  simp [negativeEtaLine, affineCoordinateLine, etaBasis]

@[simp] theorem negativeEtaLine_theta (p : FlatCoordinatePoint) (t : ℝ) :
    negativeEtaLine p t 1 = p 1 := by
  simp [negativeEtaLine, affineCoordinateLine, etaBasis]

@[simp] theorem thetaLine_eta (p : FlatCoordinatePoint) (t : ℝ) :
    thetaLine p t 0 = p 0 := by
  simp [thetaLine, affineCoordinateLine, thetaBasis]

@[simp] theorem thetaLine_theta (p : FlatCoordinatePoint) (t : ℝ) :
    thetaLine p t 1 = p 1 + t := by
  simp [thetaLine, affineCoordinateLine, thetaBasis]

/-- The negative-`η` coordinate line is flat-affine geodesic. -/
theorem negativeEtaLine_isFlatAffineGeodesic (p : FlatCoordinatePoint) :
    IsFlatAffineGeodesic (negativeEtaLine p) := by
  exact affineCoordinateLine_isFlatAffineGeodesic p (-etaBasis)

/-- The constant-`η` / varying-`θ` coordinate line is flat-affine geodesic. -/
theorem thetaLine_isFlatAffineGeodesic (p : FlatCoordinatePoint) :
    IsFlatAffineGeodesic (thetaLine p) := by
  exact affineCoordinateLine_isFlatAffineGeodesic p thetaBasis

/-- The two logarithmic coordinate directions are orthogonal. -/
theorem etaBasis_thetaBasis_orthogonal :
    planeDot etaBasis thetaBasis = 0 := by
  simp [planeDot, etaBasis, thetaBasis]

/-- The `η` coordinate gradient has unit squared norm. -/
theorem etaBasis_normSq : planeNormSq etaBasis = 1 := by
  simp [planeNormSq, planeDot, etaBasis]

/-- The `θ` coordinate gradient has unit squared norm. -/
theorem thetaBasis_normSq : planeNormSq thetaBasis = 1 := by
  simp [planeNormSq, planeDot, thetaBasis]

/-- Negative `η` direction also has unit squared norm. -/
theorem neg_etaBasis_normSq : planeNormSq (-etaBasis) = 1 := by
  simp [planeNormSq, planeDot, etaBasis]

/-- The coordinate-line velocities are orthogonal and unit. -/
theorem bipolar_flat_coordinate_frame_packet :
    planeDot (-etaBasis) thetaBasis = 0 ∧
      planeNormSq (-etaBasis) = 1 ∧
      planeNormSq thetaBasis = 1 := by
  exact ⟨by simp [planeDot, etaBasis, thetaBasis],
    neg_etaBasis_normSq,
    thetaBasis_normSq⟩

/-- Compact geodesic-coordinate packet. -/
theorem bipolar_flat_coordinate_geodesic_packet
    (p : FlatCoordinatePoint) :
    IsFlatAffineGeodesic (negativeEtaLine p) ∧
      IsFlatAffineGeodesic (thetaLine p) ∧
      (∀ t, negativeEtaLine p t 1 = p 1) ∧
      (∀ t, thetaLine p t 0 = p 0) := by
  exact ⟨negativeEtaLine_isFlatAffineGeodesic p,
    thetaLine_isFlatAffineGeodesic p,
    negativeEtaLine_theta p,
    thetaLine_eta p⟩

end InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
