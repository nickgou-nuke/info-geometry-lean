import Mathlib.Tactic

/-!
# Finite tripotent algebra

This module records elementary algebraic consequences of a supplied tripotent
operator `op^3 = op` in an arbitrary ring.

It does **not** prove emergent spacetime, physical supercharges, or a universal
classification of particles.  It proves only that `op^2` is idempotent and that
`op` commutes with its own square.
-/

namespace InfoGeometry.Topology.Tripotent

variable {R : Type*} [Ring R]

/-- A supplied tripotent element: `op^3 = op`.

This is a direct algebraic relation rather than a typeclass: tripotency is
data about the element, not ambient structure on the ring. -/
def IsTripotent (op : R) : Prop :=
  op ^ 3 = op

namespace IsTripotent

end IsTripotent

/-- If `op^3 = op`, then `op^2` is idempotent. -/
theorem tripotent_square_is_idempotent (op : R) (h : IsTripotent op) :
    (op ^ 2) * (op ^ 2) = op ^ 2 := by
  calc
    (op ^ 2) * (op ^ 2) = (op ^ 3) * op := by noncomm_ring
    _ = op * op := by rw [h]
    _ = op ^ 2 := by rw [pow_two]

/-- Compatibility name for the finite idempotent consequence. -/
theorem emergent_spacetime_projector (op : R) (h : IsTripotent op) :
    (op ^ 2) * (op ^ 2) = op ^ 2 :=
  tripotent_square_is_idempotent op h

/-- Any element commutes with its own square. -/
theorem tripotent_commutes_with_square (op : R) :
    op * (op ^ 2) = (op ^ 2) * op := by
  noncomm_ring

/-- Compatibility name for the finite commutation consequence. -/
theorem supercharge_conservation (op : R) (h : IsTripotent op) :
    op * (op ^ 2) = (op ^ 2) * op :=
  tripotent_commutes_with_square op

end InfoGeometry.Topology.Tripotent
