import Mathlib
import InfoGeometry.Canonical.A2QutritTransitionRootBridge
import InfoGeometry.Canonical.SixStateD6C2S3

/-!
# The concrete `D₆` action on the six `A₂` roots

The existing `A2InsideD5RootSubsystem` owner supplies the six ordered roots,
the faithful coordinate `S₃` action, and the antipodal involution.  The
existing `SixStateD6C2S3` owner supplies the concrete factorisation
`D₆ ≃* C₂ × S₃`.  This file composes those existing maps into a direct
permutation representation on the six-root carrier.

This is an action theorem only.  It does not identify the six-state matrix
operators with qutrit transition matrices or claim a continuous `SU(3)`
representation.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.SixStateD6A2RootBridge

open InfoGeometry.Canonical.A2InsideD5RootSubsystem
open InfoGeometry.Canonical.A2QutritTransitionRootBridge
open InfoGeometry.Canonical.A2WeylFin3Action
open InfoGeometry.Canonical.SixStateD6C2S3

abbrev D6 := DihedralGroup 6
abbrev RootPermutation := Equiv.Perm A2Root

def oppositeRootEquiv : RootPermutation where
  toFun := oppositeRoot
  invFun := oppositeRoot
  left_inv := oppositeRoot_involutive
  right_inv := oppositeRoot_involutive

@[simp] theorem oppositeRootEquiv_apply (r : A2Root) :
    oppositeRootEquiv r = oppositeRoot r := rfl

@[simp] theorem oppositeRootEquiv_sq :
    oppositeRootEquiv ^ 2 = 1 := by
  apply Equiv.ext
  intro r
  simpa [oppositeRootEquiv, pow_two] using oppositeRoot_involutive r

theorem oppositeRootEquiv_comm_weyl (σ : Equiv.Perm (Fin 3)) :
    oppositeRootEquiv * weylAction σ =
      weylAction σ * oppositeRootEquiv := by
  apply Equiv.ext
  intro r
  exact (oppositeRoot_weylAction_commute σ r).symm

private def d6RootActionMap : D6 → RootPermutation
  | .r i =>
      (oppositeRootEquiv ^ (i.val % 2)) *
        weylAction (shiftC3 ^ (i.val % 3))
  | .sr i =>
      (oppositeRootEquiv ^ (i.val % 2)) *
        weylAction (rho3 * shiftC3 ^ (i.val % 3))

private theorem d6RootActionMap_one :
    d6RootActionMap (1 : D6) = 1 := by
  change d6RootActionMap (.r 0) = 1
  native_decide

private theorem d6RootActionMap_mul (a b : D6) :
    d6RootActionMap (a * b) = d6RootActionMap a * d6RootActionMap b := by
  revert a b
  native_decide

def d6RootAction : D6 →* RootPermutation where
  toFun := d6RootActionMap
  map_one' := d6RootActionMap_one
  map_mul' := d6RootActionMap_mul

theorem d6RootAction_apply_r (i : ZMod 6) :
    d6RootAction (.r i) =
      (oppositeRootEquiv ^ (i.val % 2)) *
        weylAction (shiftC3 ^ (i.val % 3)) := rfl

theorem d6RootAction_apply_sr (i : ZMod 6) :
    d6RootAction (.sr i) =
      (oppositeRootEquiv ^ (i.val % 2)) *
        weylAction (rho3 * shiftC3 ^ (i.val % 3)) := rfl

theorem d6RootAction_preserves_root_norm (g : D6) (r : A2Root) :
    dot (a2RootVector (d6RootAction g r))
        (a2RootVector (d6RootAction g r)) = 2 := by
  exact a2RootVector_norm _

theorem d6RootAction_preserves_root_pairing (g : D6) (r s : A2Root) :
    dot (a2RootVector (d6RootAction g r))
        (a2RootVector (d6RootAction g s)) =
      dot (a2RootVector r) (a2RootVector s) := by
  revert g r s
  native_decide

theorem d6RootAction_injective : Function.Injective d6RootAction := by
  native_decide

end InfoGeometry.Canonical.SixStateD6A2RootBridge
