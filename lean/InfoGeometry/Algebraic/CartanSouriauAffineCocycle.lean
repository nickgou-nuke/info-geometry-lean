import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Logic.Equiv.Defs

/-!
# Finite affine coadjoint cocycles

This file isolates the algebraic part of an affine Souriau moment-map law.
The coadjoint action is represented abstractly by additive endomorphisms of a
dual space.  No Lie-group, differentiability, or arithmetic hypotheses are
introduced here.
-/

namespace InfoGeometry.Algebraic.CartanSouriauAffineCocycle

variable {G M : Type*} [Group G] [AddCommGroup M]

structure Datum where
  dualAction : G → M →+ M
  dualAction_one : dualAction 1 = AddMonoidHom.id M
  dualAction_mul : ∀ g h,
    dualAction (g * h) = (dualAction g).comp (dualAction h)
  theta : G → M
  theta_one : theta 1 = 0
  theta_mul : ∀ g h,
    theta (g * h) = theta g + dualAction g (theta h)

structure AffineMomentMap (D : Datum (G := G) (M := M)) (X : Type*) where
  stateAction : G → X → X
  stateAction_one : stateAction 1 = id
  stateAction_mul : ∀ g h,
    stateAction (g * h) = (stateAction g) ∘ (stateAction h)
  moment : X → M
  moment_affine_equivariant : ∀ g x,
    moment (stateAction g x) =
      D.dualAction g (moment x) + D.theta g

theorem AffineMomentMap.moment_affine_equivariant_apply
    (D : Datum (G := G) (M := M)) (X : Type*)
    (A : AffineMomentMap D X) (g : G) (x : X) :
    A.moment (A.stateAction g x) =
      D.dualAction g (A.moment x) + D.theta g :=
  A.moment_affine_equivariant g x

def affineAction (D : Datum (G := G) (M := M)) (g : G) (μ : M) : M :=
  D.dualAction g μ + D.theta g

theorem affineAction_one (D : Datum (G := G) (M := M)) (μ : M) :
    affineAction D 1 μ = μ := by
  rw [affineAction, D.dualAction_one, D.theta_one]
  simp

theorem affineAction_mul (D : Datum (G := G) (M := M)) (g h : G) (μ : M) :
    affineAction D (g * h) μ = affineAction D g (affineAction D h μ) := by
  rw [affineAction, D.dualAction_mul, D.theta_mul]
  simp only [AddMonoidHom.comp_apply, affineAction]
  rw [map_add]
  simp only [add_comm, add_left_comm]

/-- The additive dual action is automatically invertible, with inverse given
by the action of the group inverse. -/
def dualActionEquiv (D : Datum (G := G) (M := M)) (g : G) : AddEquiv M M where
  toFun := D.dualAction g
  invFun := D.dualAction g⁻¹
  map_add' := (D.dualAction g).map_add
  left_inv := by
    intro μ
    have h := congrArg (fun T : M →+ M => T μ)
      (D.dualAction_mul g⁻¹ g)
    simpa [inv_mul_cancel, D.dualAction_one, AddMonoidHom.comp_apply] using h.symm
  right_inv := by
    intro μ
    have h := congrArg (fun T : M →+ M => T μ)
      (D.dualAction_mul g g⁻¹)
    simpa [mul_inv_cancel, D.dualAction_one, AddMonoidHom.comp_apply] using h.symm

/-- The affine action is an equivalence; its inverse is the affine action of
the group inverse. -/
def affineActionEquiv (D : Datum (G := G) (M := M)) (g : G) : Equiv M M where
  toFun := affineAction D g
  invFun := affineAction D g⁻¹
  left_inv := by
    intro μ
    simpa [← affineAction_mul, affineAction_one]
  right_inv := by
    intro μ
    simpa [← affineAction_mul, affineAction_one]

theorem theta_cocycle (D : Datum (G := G) (M := M)) (g h : G) :
    D.theta (g * h) = D.theta g + D.dualAction g (D.theta h) :=
  D.theta_mul g h

theorem affineAction_isAffine (D : Datum (G := G) (M := M)) (g : G)
    (μ ν : M) :
    affineAction D g (μ + ν) =
      affineAction D g μ + D.dualAction g ν := by
  simp [affineAction, add_comm, add_left_comm]

theorem affineAction_sub (D : Datum (G := G) (M := M))
    (g : G) (μ ν : M) :
    affineAction D g μ - affineAction D g ν =
      D.dualAction g (μ - ν) := by
  simp [affineAction, map_sub, sub_eq_add_neg, add_assoc, add_comm,
    add_left_comm]

theorem AffineMomentMap.moment_eq_affineAction
    (D : Datum (G := G) (M := M)) (X : Type*)
    (A : AffineMomentMap D X) (g : G) (x : X) :
    A.moment (A.stateAction g x) =
      affineAction D g (A.moment x) :=
  A.moment_affine_equivariant g x

/- The affine cocycle disappears from differences of moment-map charges. -/
theorem AffineMomentMap.moment_sub_eq_dualAction
    (D : Datum (G := G) (M := M)) (X : Type*)
    (A : AffineMomentMap D X) (g : G) (x y : X) :
    A.moment (A.stateAction g x) - A.moment (A.stateAction g y) =
      D.dualAction g (A.moment x - A.moment y) := by
  rw [A.moment_eq_affineAction, A.moment_eq_affineAction]
  exact affineAction_sub D g (A.moment x) (A.moment y)

end InfoGeometry.Algebraic.CartanSouriauAffineCocycle
