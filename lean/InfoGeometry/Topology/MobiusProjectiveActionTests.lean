import InfoGeometry.Topology.MobiusProjectiveAction

open InfoGeometry
open InfoGeometry.Topology.MobiusProjectiveAction

example (point : RiemannSphere) : (1 : PGL2C) • point = point :=
  one_smul PGL2C point

example (first second : PGL2C) (point : RiemannSphere) :
    (first * second) • point = first • (second • point) :=
  mul_smul first second point

example (transformation : PGL2C) (point : RiemannSphere) :
    transformation⁻¹ • (transformation • point) = point :=
  inv_smul_smul transformation point

example (first second : PGL2C)
    (equalActions : ∀ point : RiemannSphere, first • point = second • point) :
    first = second :=
  (eq_iff_same_action first second).mpr equalActions

example (point : CP1) (transformation : MobiusTransform) :
    (Quotient.mk' transformation : PGL2C) • point.toRiemannSphere =
      (transformation.actCP1 point).toRiemannSphere :=
  mk_smul_toRiemannSphere transformation point

#print axioms pglActionHom_injective
#print axioms mk_smul_toRiemannSphere
