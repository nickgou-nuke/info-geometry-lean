import Mathlib.Tactic
import InfoGeometry.Topology.AharonovBohmVortices
import InfoGeometry.Topology.ParafermionBraiding

/-!
# Finite order-two/order-three compatibility packet

This module packages two explicitly supplied finite phase certificates: one
order-two phase and one order-three Aharonov--Bohm vortex phase.  Their product
identity is a simple finite algebraic consequence.

It does **not** prove grand unification, Lorentz/color unification, physical
supersymmetry, or confinement.  The historical name of the file is retained as
a compatibility location for finite topology definitions.
-/

namespace InfoGeometry.Topology.GrandUnification

open Complex InfoGeometry.Topology.Parafermion

/-- A finite compatibility packet with an order-two phase and an order-three vortex. -/
structure UnifiedVacuum where
  orderTwoPhase : ℂ
  h_order_two : orderTwoPhase ^ 2 = 1
  vortex : AharonovBohmVortex

/--
Compatibility name for the finite order-two/order-three phase identity.

The statement says only that explicitly supplied order-two and order-three
certificates multiply to `1`.
-/
theorem grand_unification_symmetry (vac : UnifiedVacuum) :
    (vac.orderTwoPhase ^ 2) * (vac.vortex.phase ^ 3) = 1 := by
  rw [vac.h_order_two, vac.vortex.h_fractional_winding]
  ring

end InfoGeometry.Topology.GrandUnification
