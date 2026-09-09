import InfoGeometry.Canonical.CanonicalZornNullProjectiveBoundaryBridge

/-!
# Homogeneous and linear null lifts for the canonical Zorn carrier

The affine conformal chart is not homogeneous in its source coordinate.  This
owner records the homogeneous quadratic lift separately and uses the linear
null inclusion for the actual projectivization of null Zorn rays.
-/

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornHomogeneousBoundaryLift

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Canonical.CanonicalZornNullProjectiveBoundaryBridge
open ProjectiveAffineConformalClosure55

structure HomogeneousPAC44 where
  t : ℝ
  x : PACSplit44

def scalePAC44 (a : ℝ) (x : PACSplit44) : PACSplit44 where
  x0 := a * x.x0
  x1 := a * x.x1
  x2 := a * x.x2
  x3 := a * x.x3
  y0 := a * x.y0
  y1 := a * x.y1
  y2 := a * x.y2
  y3 := a * x.y3

def scaleHomogeneous (a : ℝ) (p : HomogeneousPAC44) : HomogeneousPAC44 where
  t := a * p.t
  x := scalePAC44 a p.x

def homogeneousConformalLift (p : HomogeneousPAC44) : PACSplit55 where
  x0 := p.t * p.x.x0
  x1 := p.t * p.x.x1
  x2 := p.t * p.x.x2
  x3 := p.t * p.x.x3
  y0 := p.t * p.x.y0
  y1 := p.t * p.x.y1
  y2 := p.t * p.x.y2
  y3 := p.t * p.x.y3
  u := (p.t ^ 2 - Q44 p.x) / 2
  v := (p.t ^ 2 + Q44 p.x) / 2

theorem homogeneousConformalLift_null (p : HomogeneousPAC44) :
    Q55 (homogeneousConformalLift p) = 0 := by
  cases p with
  | mk t x =>
    cases x
    simp [homogeneousConformalLift, Q55, Q44]
    ring

theorem homogeneousConformalLift_scale (a : ℝ) (p : HomogeneousPAC44) :
    homogeneousConformalLift (scaleHomogeneous a p) =
      smul55 (a ^ 2) (homogeneousConformalLift p) := by
  cases p with
  | mk t x =>
    cases x
    congr 1 <;>
      simp [homogeneousConformalLift, scaleHomogeneous, scalePAC44, smul55, Q44] <;>
        ring <;> simp

theorem homogeneousConformalLift_ne_zero_of_time_ne_zero
    (p : HomogeneousPAC44) (ht : p.t ≠ 0) :
    homogeneousConformalLift p ≠
      CanonicalZornNullProjectiveBoundaryBridge.pacSplit55Zero := by
  intro h
  have hu := congrArg PACSplit55.u h
  have hv := congrArg PACSplit55.v h
  dsimp [homogeneousConformalLift,
    CanonicalZornNullProjectiveBoundaryBridge.pacSplit55Zero] at hu hv
  have hu' : (p.t ^ 2 - Q44 p.x) / 2 = 0 := by
    simpa using hu
  have hv' : (p.t ^ 2 + Q44 p.x) / 2 = 0 := by
    simpa using hv
  have : p.t ^ 2 = 0 := by linarith
  exact ht (sq_eq_zero_iff.mp this)

def linearNullPAC55 (x : PACSplit44) : PACSplit55 where
  x0 := x.x0
  x1 := x.x1
  x2 := x.x2
  x3 := x.x3
  y0 := x.y0
  y1 := x.y1
  y2 := x.y2
  y3 := x.y3
  u := 0
  v := 0

def linearNullBoundaryLift (Z : CanonicalZorn) : PACSplit55 :=
  linearNullPAC55 (canonicalToPAC44 Z)

theorem linearNullPAC55_Q55 (x : PACSplit44) :
    Q55 (linearNullPAC55 x) = Q44 x := by
  cases x
  simp [linearNullPAC55, Q55, Q44]

theorem linearNullBoundaryLift_Q55 {Z : CanonicalZorn}
    (hZ : canonicalDet Z = 0) :
    Q55 (linearNullBoundaryLift Z) = 0 := by
  rw [linearNullBoundaryLift, linearNullPAC55_Q55,
    canonicalToPAC44_Q44, hZ]

end InfoGeometry.Canonical.CanonicalZornHomogeneousBoundaryLift
