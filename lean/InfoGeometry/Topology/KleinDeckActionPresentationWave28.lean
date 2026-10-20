/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinQuotientDeckInvariants

namespace InfoGeometry.Topology.KleinQuotientDeckInvariants
namespace KleinDeckGroup

/-- The affine deck action realizes the Klein presentation relation by conjugation:
    the orientation-reversing generator sends the longitudinal translation to
    its inverse on the actual plane carrier. -/
theorem deckAction_b_conj_a (p : PlanePoint) :
    deckAction b (deckAction a (deckAction (inv b) p)) =
      deckAction (inv a) p := by
  rw [← deckAction_mul, ← deckAction_mul]
  have hgroup : mul (mul b a) (inv b) = inv a := by
    norm_num [mul, inv, a, b, signZ]
  rw [hgroup]

/-- The same relation in the equivalent four-factor presentation. -/
theorem deckAction_babInv_a (p : PlanePoint) :
    deckAction b (deckAction a (deckAction (inv b) (deckAction a p))) = p := by
  rw [deckAction_b_conj_a]
  rw [← deckAction_mul]
  rw [mul_left_inv]
  exact deckAction_one p

end KleinDeckGroup
end InfoGeometry.Topology.KleinQuotientDeckInvariants
