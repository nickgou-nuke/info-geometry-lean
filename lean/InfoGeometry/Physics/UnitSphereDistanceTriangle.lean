import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
The metric triangle inequality on the unit sphere is inherited from the
ambient metric.  This is the canonical Mathlib carrier for the first step of
an angular-distance construction: points are elements of the metric sphere
with its induced metric, so no extra geometric axiom is introduced.
-/

namespace InfoGeometry.Physics

universe u

set_option linter.unusedSectionVars false

variable {E : Type u} [NormedAddCommGroup E]

abbrev UnitSphere (E : Type u) [NormedAddCommGroup E] : Type u :=
  {x : E // x ∈ Metric.sphere (0 : E) 1}

def unitSphereDistance (x y : UnitSphere E) : ℝ := dist x y

theorem unitSphereDistance_triangle (x y z : UnitSphere E) :
    unitSphereDistance x z ≤ unitSphereDistance x y + unitSphereDistance y z := by
  exact dist_triangle x y z

theorem unitSphereDistance_self (x : UnitSphere E) :
    unitSphereDistance x x = 0 := by
  exact dist_self x

theorem unitSphereDistance_comm (x y : UnitSphere E) :
    unitSphereDistance x y = unitSphereDistance y x := by
  exact dist_comm x y

theorem unitSphere_norm (x : UnitSphere E) : ‖(x : E)‖ = 1 := by
  have h := x.property
  rw [Metric.mem_sphere, dist_zero_right] at h
  exact h

variable [InnerProductSpace ℝ E]

noncomputable def unitSphereAngularAngle (x y : UnitSphere E) : ℝ :=
  InnerProductGeometry.angle (x : E) (y : E)

theorem unitSphereAngularAngle_eq_arccos_inner (x y : UnitSphere E) :
    unitSphereAngularAngle x y = Real.arccos (inner ℝ (x : E) (y : E)) := by
  unfold unitSphereAngularAngle InnerProductGeometry.angle
  rw [unitSphere_norm x, unitSphere_norm y, mul_one, div_one]

theorem angular_distance_triangle_of_metric_realization
    (d : UnitSphere E → UnitSphere E → ℝ)
    (hd : ∀ x y, d x y = unitSphereDistance x y)
    (x y z : UnitSphere E) :
    d x z ≤ d x y + d y z := by
  rw [hd, hd, hd]
  exact unitSphereDistance_triangle x y z

end InfoGeometry.Physics
