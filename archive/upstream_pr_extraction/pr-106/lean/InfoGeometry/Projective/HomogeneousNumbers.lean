import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Projective.HomogeneousNumbers

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def projCoord (x y : ℝ) : ℝ × ℝ := (x, y)

def projScale (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (c * p.1, c * p.2)

theorem proj_scaling_ratio (x y c : ℝ) (hy : y ≠ 0) (hc : c ≠ 0) :
    (projScale c (projCoord x y)).1 / (projScale c (projCoord x y)).2 = x / y := by
  unfold projScale projCoord
  dsimp
  rw [mul_div_mul_left x y hc]

theorem grand_homogeneous_numbers_synthesis (x y c : ℝ) (hy : y ≠ 0) (hc : c ≠ 0) :
    (projScale c (projCoord x y)).1 / (projScale c (projCoord x y)).2 = x / y :=
  proj_scaling_ratio x y c hy hc

end
end InfoGeometry.Projective.HomogeneousNumbers
