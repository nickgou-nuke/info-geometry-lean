import Mathlib

/-!
# Inverse mirror for a group

The map sending `g` to `op (g⁻¹)` is a monoid equivalence from a group to its
opposite.  The opposite is essential: inversion reverses multiplication order.
-/

namespace InfoGeometry.Categorical.PolarizedBraidMirror

variable {B : Type*} [Group B]

def inverseMirror : B ≃* Bᵐᵒᵖ where
  toFun g := MulOpposite.op g⁻¹
  invFun g := (MulOpposite.unop g)⁻¹
  left_inv g := by simp
  right_inv g := by simp
  map_mul' a b := by simp

@[simp] theorem inverseMirror_apply (g : B) :
    inverseMirror g = MulOpposite.op g⁻¹ := rfl

end InfoGeometry.Categorical.PolarizedBraidMirror
