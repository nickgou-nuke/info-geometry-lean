import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Scaling audit for the affine `(4,4) -> (5,5)` conformal chart

The concrete `conformalEmbed44to55` is an affine-chart lift into the null
cone.  It is not a homogeneous linear map on the `(4,4)` carrier.  This
owner records that boundary explicitly, so an annihilator projectivization
is not introduced through an invalid quotient descent.
-/

noncomputable section

namespace ProjectiveAffineConformalClosure55

def scale44 (a : ℝ) (x : PACSplit44) : PACSplit44 where
  x0 := a * x.x0
  x1 := a * x.x1
  x2 := a * x.x2
  x3 := a * x.x3
  y0 := a * x.y0
  y1 := a * x.y1
  y2 := a * x.y2
  y3 := a * x.y3

def unit44 : PACSplit44 where
  x0 := 1
  x1 := 0
  x2 := 0
  x3 := 0
  y0 := 0
  y1 := 0
  y2 := 0
  y3 := 0

theorem scale44_two_unit44 : scale44 2 unit44 =
    { x0 := 2, x1 := 0, x2 := 0, x3 := 0,
      y0 := 0, y1 := 0, y2 := 0, y3 := 0 } := by
  simp [scale44, unit44]

theorem conformalEmbed44to55_not_projectively_homogeneous_at_unit44 :
    ¬ sameProjectiveLine55
        (conformalEmbed44to55 unit44)
        (conformalEmbed44to55 (scale44 2 unit44)) := by
  intro h
  rcases h with ⟨a, ha, hEq⟩
  have hx0 := congrArg PACSplit55.x0 hEq
  have hu := congrArg PACSplit55.u hEq
  have ha2 : a = 2 := by
    simpa [conformalEmbed44to55, unit44, scale44, smul55] using hx0.symm
  rw [ha2] at hu
  norm_num [conformalEmbed44to55, unit44, scale44, Q44, smul55] at hu

end ProjectiveAffineConformalClosure55
