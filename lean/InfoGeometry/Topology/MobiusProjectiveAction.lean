import Experimental.Sandbox.Mobius.EvalEquiv
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Group.Action.Faithful

noncomputable section

namespace InfoGeometry.Topology.MobiusProjectiveAction

open Experimental.Sandbox.Mobius

def pglActionHom : PGL2C →* Equiv.Perm RiemannSphere where
  toFun := Quotient.lift mobiusEvalEquiv (by
    intro first second equivalent
    apply Equiv.ext
    intro point
    exact equivalent point)
  map_one' := by
    apply Equiv.ext
    intro point
    exact InfoGeometry.eval_default point
  map_mul' first second := by
    refine Quotient.inductionOn₂ first second ?_
    intro firstRepresentative secondRepresentative
    apply Equiv.ext
    intro point
    exact InfoGeometry.eval_comp firstRepresentative secondRepresentative point

@[simp] theorem pglActionHom_mk (transformation : MobiusTransform) :
    pglActionHom (Quotient.mk' transformation) = mobiusEvalEquiv transformation := rfl

theorem pglActionHom_injective : Function.Injective pglActionHom := by
  intro first second
  refine Quotient.inductionOn₂ first second ?_
  intro firstRepresentative secondRepresentative equalActions
  apply Quotient.sound
  intro point
  exact congrArg (fun action : Equiv.Perm RiemannSphere => action point) equalActions

instance pglMulAction : MulAction PGL2C RiemannSphere :=
  MulAction.compHom RiemannSphere pglActionHom

@[simp] theorem mk_smul (transformation : MobiusTransform) (point : RiemannSphere) :
    (Quotient.mk' transformation : PGL2C) • point = transformation.eval point := rfl

instance pglFaithfulSMul : FaithfulSMul PGL2C RiemannSphere where
  eq_of_smul_eq_smul := by
    intro first second equalActions
    apply pglActionHom_injective
    apply Equiv.ext
    intro point
    exact equalActions point

theorem eq_iff_same_action (first second : PGL2C) :
    first = second ↔ ∀ point : RiemannSphere, first • point = second • point := by
  constructor
  · intro equalElements
    subst second
    intro point
    rfl
  · exact FaithfulSMul.eq_of_smul_eq_smul

theorem mk_smul_toRiemannSphere (transformation : MobiusTransform) (point : CP1) :
    (Quotient.mk' transformation : PGL2C) • point.toRiemannSphere =
      (transformation.actCP1 point).toRiemannSphere := by
  rw [mk_smul]
  exact (InfoGeometry.mobius_action_correspondence transformation point).symm

end InfoGeometry.Topology.MobiusProjectiveAction
