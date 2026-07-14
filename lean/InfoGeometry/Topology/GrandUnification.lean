import Mathlib
import InfoGeometry.Topology.AharonovBohmVortices
import InfoGeometry.Topology.ParafermionBraiding

/-!
# Finite order-two/order-three compatibility packet

This module packages two explicitly supplied finite phase certificates: one
order-two phase and one order-three Aharonov--Bohm vortex phase.  Their product
identity is a simple finite algebraic consequence.

It does **not** prove grand unification, Lorentz/color unification, physical
supersymmetry, or confinement.  The historical name of the file is retained as
a compatibility location for finite topology sockets.
-/

namespace GrandUnification

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

/-- The finite braid relation is available alongside the order packet. -/
theorem order_packet_with_burau_braid (vac : UnifiedVacuum) (t : ℂ) :
    (vac.orderTwoPhase ^ 2) * (vac.vortex.phase ^ 3) = 1 ∧
      sigma_1 t * sigma_2 t * sigma_1 t = sigma_2 t * sigma_1 t * sigma_2 t := by
  exact ⟨grand_unification_symmetry vac, su3_parafermion_braiding t⟩

end GrandUnification
