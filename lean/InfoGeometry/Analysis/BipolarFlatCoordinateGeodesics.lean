import InfoGeometry.Analysis.BipolarOrthogonalFlowSplit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Tactic

/-!
# Flat affine geodesics in bipolar logarithmic coordinates

The pullback metric associated with a local logarithmic chart is Euclidean in
coordinates `(η, θ)`: `dη² + dθ²`. This file formalizes the safe affine content
of that statement.

Every curve `p + t v` is represented by Mathlib's native `AffineMap.lineMap`,
has constant derivative `v`, zero derivative of its velocity, and zero centered
second difference. In particular:

* the negative-`η` coordinate line keeps `θ` fixed;
* the `θ` coordinate line keeps `η` fixed;
* both have unit coordinate speed and orthogonal velocities.

These are the coordinate representatives of local geodesics in a flat
`(η,θ)` chart. No global Riemannian manifold, Levi-Civita connection, or claim
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

/-- Unit coordinate vector in the `η` direction. -/
def etaBasis : PlaneCovector := ![1, 0]

/-- Unit coordinate vector in the `θ` direction. -/
def thetaBasis : PlaneCovector := ![0, 1]

/-- Flat affine line with initial point `p` and constant velocity `v`. -/
def affineCoordinateLine
    (p v : PlaneCovector) (t : ℝ) : PlaneCovector :=
  p + t • v

/-- The native affine-map owner of `affineCoordinateLine`. -/
def affineCoordinateMap
    (p v : PlaneCovector) : ℝ →ᵃ[ℝ] PlaneCovector :=
  AffineMap.lineMap p (p + v)

/-- The native affine map evaluates to the elementary coordinate formula. -/
theorem affineCoordinateMap_apply
    (p v : PlaneCovector) (t : ℝ) :
    affineCoordinateMap p v t = affineCoordinateLine p v t := by
  ext i
  fin_cases i <;>
    simp [affineCoordinateMap, affineCoordinateLine,
      AffineMap.lineMap_apply_module'] <;>
    ring

/-- Native Mathlib derivative theorem for a flat coordinate line. -/
theorem hasDerivAt_affineCoordinateLine
    (p v : PlaneCovector) (t : ℝ) :
    HasDerivAt (affineCoordinateLine p v) v t := by
  have h :=
    AffineMap.hasDerivAt_lineMap
      (𝕜 := ℝ) (a := p) (b := p + v) (x := t)
  have hfun :
      (AffineMap.lineMap p (p + v) : ℝ → PlaneCovector) =
        affineCoordinateLine p v := by
    funext u
    exact affineCoordinateMap_apply p v u
  rw [hfun] at h
  simpa using h

/-- Ordinary derivative readout of the constant velocity. -/
theorem deriv_affineCoordinateLine
    (p v : PlaneCovector) (t : ℝ) :
    deriv (affineCoordinateLine p v) t = v :=
  (hasDerivAt_affineCoordinateLine p v t).deriv

/-- The velocity field of an affine coordinate line has zero derivative. -/
theorem hasDerivAt_affineCoordinateVelocity_zero
    (p v : PlaneCovector) (t : ℝ) :
    HasDerivAt (fun u : ℝ => deriv (affineCoordinateLine p v) u) 0 t := by
  have hfun :
      (fun u : ℝ => deriv (affineCoordinateLine p v) u) =
        fun _ : ℝ => v := by
    funext u
    exact deriv_affineCoordinateLine p v u
  rw [hfun]
  exact hasDerivAt_const t v

/-- Zero acceleration readout in native derivative notation. -/
theorem deriv_velocity_affineCoordinateLine_zero
    (p v : PlaneCovector) (t : ℝ) :
    deriv (fun u : ℝ => deriv (affineCoordinateLine p v) u) t = 0 :=
  (hasDerivAt_affineCoordinateVelocity_zero p v t).deriv

/-- Centered second difference of a coordinate curve. -/
def centeredSecondDifference
    (γ : ℝ → PlaneCovector) (t h : ℝ) : PlaneCovector :=
  γ (t + h) - (2 : ℝ) • γ t + γ (t - h)

/-- Finite affine-geodesic predicate for the flat coordinate carrier. -/
def IsFlatAffineGeodesic (γ : ℝ → PlaneCovector) : Prop :=
  ∀ t h, centeredSecondDifference γ t h = 0

/-- Every constant-velocity affine line has zero centered second difference. -/
theorem affineCoordinateLine_isFlatAffineGeodesic
    (p v : PlaneCovector) :
    IsFlatAffineGeodesic (affineCoordinateLine p v) := by
  intro t h
  ext i
  fin_cases i <;>
    simp [centeredSecondDifference, affineCoordinateLine] <;>
    ring

/-- Exact increment law for an affine coordinate line. -/
theorem affineCoordinateLine_increment
    (p v : PlaneCovector) (t h : ℝ) :
    affineCoordinateLine p v (t + h) - affineCoordinateLine p v t = h • v := by
  ext i
  fin_cases i <;> simp [affineCoordinateLine] <;> ring

/-- Barycentric affine-line identity. -/
theorem affineCoordinateLine_barycentric
    (p v : PlaneCovector) (a t u : ℝ) :
    affineCoordinateLine p v ((1 - a) * t + a * u) =
      (1 - a) • affineCoordinateLine p v t +
        a • affineCoordinateLine p v u := by
  ext i
  fin_cases i <;> simp [affineCoordinateLine] <;> ring

/-- Coordinate line following the negative `η` gradient direction. -/
def negativeEtaLine (p : PlaneCovector) (t : ℝ) : PlaneCovector :=
  affineCoordinateLine p (-etaBasis) t

/-- Coordinate line following the positive `θ` direction. -/
def thetaLine (p : PlaneCovector) (t : ℝ) : PlaneCovector :=
  affineCoordinateLine p thetaBasis t

@[simp] theorem negativeEtaLine_eta (p : PlaneCovector) (t : ℝ) :
    negativeEtaLine p t 0 = p 0 - t := by
  simp [negativeEtaLine, affineCoordinateLine, etaBasis]
  ring

@[simp] theorem negativeEtaLine_theta (p : PlaneCovector) (t : ℝ) :
    negativeEtaLine p t 1 = p 1 := by
  simp [negativeEtaLine, affineCoordinateLine, etaBasis]

@[simp] theorem thetaLine_eta (p : PlaneCovector) (t : ℝ) :
    thetaLine p t 0 = p 0 := by
  simp [thetaLine, affineCoordinateLine, thetaBasis]

@[simp] theorem thetaLine_theta (p : PlaneCovector) (t : ℝ) :
    thetaLine p t 1 = p 1 + t := by
  simp [thetaLine, affineCoordinateLine, thetaBasis]

/-- The negative-`η` coordinate line is flat-affine geodesic. -/
theorem negativeEtaLine_isFlatAffineGeodesic (p : PlaneCovector) :
    IsFlatAffineGeodesic (negativeEtaLine p) := by
  exact affineCoordinateLine_isFlatAffineGeodesic p (-etaBasis)

/-- The constant-`η` / varying-`θ` coordinate line is flat-affine geodesic. -/
theorem thetaLine_isFlatAffineGeodesic (p : PlaneCovector) :
    IsFlatAffineGeodesic (thetaLine p) := by
  exact affineCoordinateLine_isFlatAffineGeodesic p thetaBasis

/-- Native derivative of the negative-`η` coordinate line. -/
theorem hasDerivAt_negativeEtaLine
    (p : PlaneCovector) (t : ℝ) :
    HasDerivAt (negativeEtaLine p) (-etaBasis) t := by
  exact hasDerivAt_affineCoordinateLine p (-etaBasis) t

/-- Native derivative of the `θ` coordinate line. -/
theorem hasDerivAt_thetaLine
    (p : PlaneCovector) (t : ℝ) :
    HasDerivAt (thetaLine p) thetaBasis t := by
  exact hasDerivAt_affineCoordinateLine p thetaBasis t

/-- Both canonical coordinate lines have zero acceleration. -/
theorem canonical_coordinate_lines_zero_acceleration
    (p : PlaneCovector) (t : ℝ) :
    deriv (fun u : ℝ => deriv (negativeEtaLine p) u) t = 0 ∧
      deriv (fun u : ℝ => deriv (thetaLine p) u) t = 0 := by
  exact ⟨deriv_velocity_affineCoordinateLine_zero p (-etaBasis) t,
    deriv_velocity_affineCoordinateLine_zero p thetaBasis t⟩

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
    (p : PlaneCovector) :
    IsFlatAffineGeodesic (negativeEtaLine p) ∧
      IsFlatAffineGeodesic (thetaLine p) ∧
      (∀ t, negativeEtaLine p t 1 = p 1) ∧
      (∀ t, thetaLine p t 0 = p 0) := by
  exact ⟨negativeEtaLine_isFlatAffineGeodesic p,
    thetaLine_isFlatAffineGeodesic p,
    negativeEtaLine_theta p,
    thetaLine_eta p⟩

/-- Derivative-level geodesic packet for the two canonical coordinate lines. -/
theorem bipolar_flat_coordinate_derivative_packet
    (p : PlaneCovector) (t : ℝ) :
    HasDerivAt (negativeEtaLine p) (-etaBasis) t ∧
      HasDerivAt (thetaLine p) thetaBasis t ∧
      deriv (fun u : ℝ => deriv (negativeEtaLine p) u) t = 0 ∧
      deriv (fun u : ℝ => deriv (thetaLine p) u) t = 0 := by
  exact ⟨hasDerivAt_negativeEtaLine p t,
    hasDerivAt_thetaLine p t,
    (canonical_coordinate_lines_zero_acceleration p t).1,
    (canonical_coordinate_lines_zero_acceleration p t).2⟩

end InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
