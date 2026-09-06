import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The finite six-mode dihedral action

This is the label/orbit layer for a six-channel spectrum.  It proves the
dihedral relations on `ZMod 6`; it does not assert that an arbitrary
permutation of six Pluecker coordinates preserves the Klein quadratic form.
That preservation is a separate representation theorem.
-/

namespace InfoGeometry.Canonical.D6SixModeAction

abbrev D6Index := ZMod 6

def rotation (k : D6Index) : D6Index ≃ D6Index where
  toFun i := i + k
  invFun i := i - k
  left_inv := by intro i; simp [sub_eq_add_neg, add_comm]
  right_inv := by intro i; simp [sub_eq_add_neg, add_comm]

def reflection : D6Index ≃ D6Index where
  toFun i := -i
  invFun i := -i
  left_inv := by intro i; simp
  right_inv := by intro i; simp

theorem rotation_apply (k i : D6Index) :
    rotation k i = i + k := rfl

theorem reflection_apply (i : D6Index) :
    reflection i = -i := rfl

theorem rotation_add (k l : D6Index) :
    rotation (k + l) = rotation k ∘ rotation l := by
  ext i
  simp [rotation, add_left_comm, add_comm]

theorem reflection_involutive :
    reflection ∘ reflection = Equiv.refl D6Index := by
  ext i
  simp [reflection]

theorem reflection_conjugates_rotation (k : D6Index) :
    reflection ∘ rotation k ∘ reflection = rotation (-k) := by
  ext i
  simp [reflection, rotation, sub_eq_add_neg, add_comm]

theorem rotation_sixth :
    rotation (6 : D6Index) = Equiv.refl D6Index := by
  ext i
  change i + (6 : D6Index) = i
  have h : (6 : D6Index) = 0 := ZMod.natCast_self 6
  rw [h, add_zero]

def modeRotate {R : Type*} (k : D6Index) (f : D6Index → R) : D6Index → R :=
  f ∘ rotation k

def modeReflect {R : Type*} (f : D6Index → R) : D6Index → R :=
  f ∘ reflection

theorem modeRotate_add {R : Type*} (k l : D6Index) (f : D6Index → R) :
    modeRotate (k + l) f = modeRotate l (modeRotate k f) := by
  funext i
  simp [modeRotate, rotation_add, Function.comp_apply]

theorem modeReflect_involutive {R : Type*} (f : D6Index → R) :
    modeReflect (modeReflect f) = f := by
  funext i
  simp [modeReflect, reflection]

theorem modeReflect_rotate_reflect {R : Type*} (k : D6Index) (f : D6Index → R) :
    modeReflect (modeRotate k (modeReflect f)) = modeRotate (-k) f := by
  funext i
  simp [modeReflect, modeRotate, reflection, rotation,
    sub_eq_add_neg, add_comm]

end InfoGeometry.Canonical.D6SixModeAction
