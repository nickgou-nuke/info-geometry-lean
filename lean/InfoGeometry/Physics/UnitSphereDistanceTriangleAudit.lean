/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import InfoGeometry.Physics.UnitSphereDistanceTriangle

/-!
# Audit Module: UnitSphereDistanceTriangleAudit

Automated kernel verification of metric triangle inequality on the unit sphere.
-/

namespace InfoGeometry.Physics.UnitSphereDistanceTriangleAudit

open InfoGeometry.Physics

universe u
variable {E : Type u} [NormedAddCommGroup E]

#check (@unitSphereDistance_triangle :
  ∀ {E : Type u} [NormedAddCommGroup E] (x y z : UnitSphere E),
    unitSphereDistance x z ≤ unitSphereDistance x y + unitSphereDistance y z)

#check (@unitSphereDistance_self :
  ∀ {E : Type u} [NormedAddCommGroup E] (x : UnitSphere E),
    unitSphereDistance x x = 0)

#check (@unitSphereDistance_comm :
  ∀ {E : Type u} [NormedAddCommGroup E] (x y : UnitSphere E),
    unitSphereDistance x y = unitSphereDistance y x)

#check (@unitSphere_norm :
  ∀ {E : Type u} [NormedAddCommGroup E] (x : UnitSphere E),
    ‖(x : E)‖ = 1)

variable [InnerProductSpace ℝ E]

#check (@unitSphereAngularAngle_eq_arccos_inner :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : UnitSphere E),
    unitSphereAngularAngle x y = Real.arccos (inner ℝ (x : E) (y : E)))

#check (@unitSphereAngularAngle_triangle :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y z : UnitSphere E),
    unitSphereAngularAngle x z ≤
      unitSphereAngularAngle x y + unitSphereAngularAngle y z)

#print axioms unitSphereDistance_triangle
#print axioms unitSphereDistance_self
#print axioms unitSphereDistance_comm
#print axioms unitSphere_norm
#print axioms unitSphereAngularAngle_eq_arccos_inner
#print axioms unitSphereAngularAngle_triangle
#print axioms angular_distance_triangle_of_metric_realization

end InfoGeometry.Physics.UnitSphereDistanceTriangleAudit
