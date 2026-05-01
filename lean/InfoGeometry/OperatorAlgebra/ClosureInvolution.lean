/-
InfoGeometry/OperatorAlgebra/ClosureInvolution.lean

Closure involution fixed-sector algebra.

Core invariant: what survives inversion is the fixed equalizer

  Fix(θ) = { x | θ x = x }.

This module is intentionally minimal and witness-first.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ClosureInvolution

/--
A linear closure involution.

Intended examples:
* charge conjugation `e⁻ ↔ e⁺`;
* grade reversal `g₋k ↔ g₊k`;
* a linearized Tomita/Möbius closure symmetry.
-/
structure LinearClosureInvolution
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  theta : V →ₗ[ℝ] V
  theta_involutive : ∀ v : V, theta (theta v) = v

namespace LinearClosureInvolution

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (C : LinearClosureInvolution V)

/-- Fixed points of the closure involution. -/
def Fixed : Submodule ℝ V where
  carrier := {v : V | C.theta v = v}
  zero_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    dsimp at hx hy ⊢
    rw [C.theta.map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    dsimp at hx ⊢
    rw [C.theta.map_smul, hx]

/-- Membership in the fixed sector is exactly invariance under `theta`. -/
theorem mem_fixed_iff
    (v : V) :
    v ∈ C.Fixed ↔ C.theta v = v :=
  Iff.rfl

/--
If `theta` swaps `x` and `y`, then the diagonal `x + y` survives.
-/
theorem diagonal_fixed_of_swap
    {x y : V}
    (hxy : C.theta x = y)
    (hyx : C.theta y = x) :
    x + y ∈ C.Fixed := by
  change C.theta (x + y) = x + y
  rw [C.theta.map_add, hxy, hyx, add_comm]

/--
If `theta` swaps `x` and `y`, then the difference `x - y` is anti-fixed.
-/
theorem difference_anti_fixed_of_swap
    {x y : V}
    (hxy : C.theta x = y)
    (hyx : C.theta y = x) :
    C.theta (x - y) = -(x - y) := by
  rw [C.theta.map_sub, hxy, hyx]
  abel

/--
Every element maps to a fixed diagonal after adding its image.
-/
theorem diagonal_with_image_fixed
    (x : V) :
    x + C.theta x ∈ C.Fixed := by
  apply C.diagonal_fixed_of_swap
  · rfl
  · exact C.theta_involutive x

/--
The closure anti-diagonal is anti-fixed.
-/
theorem anti_diagonal_with_image
    (x : V) :
    C.theta (x - C.theta x) = -(x - C.theta x) := by
  apply C.difference_anti_fixed_of_swap
  · rfl
  · exact C.theta_involutive x

end LinearClosureInvolution

end InfoGeometry.OperatorAlgebra.ClosureInvolution
