import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Module.Basic

/-!
# Deformation positivity

This module records the minimal cone/dual-cone interface needed for a
variation-theoretic rigidity statement on a network branch.

It does not claim that an `E8` root lattice alone forces a global minimum.
The only theorem proved here is the local readback:

* if the first variation lies in the dual cone, then it is nonnegative on the
  admissible cone.

That is the Lean-safe starting point for any later action-minimization layer.
-/

namespace InfoGeometry.Network

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]

/-- A local admissible deformation is nonnegative under the first variation. -/
theorem local_first_variation_nonnegative
    (C : Set V)
    (firstVariation : V →ₗ[R] R)
    (firstVariation_dual : ∀ x ∈ C, 0 ≤ firstVariation x)
    (ξ : V)
    (hξ : ξ ∈ C) :
    0 ≤ firstVariation ξ :=
  firstVariation_dual ξ hξ

end InfoGeometry.Network
