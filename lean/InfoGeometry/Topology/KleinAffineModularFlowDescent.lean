/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinAffineOrbitQuotient
import InfoGeometry.Physics.TomitaTakesakiModularFlow

/-!
# Modular flow on the affine Klein orbit quotient

The existing affine quotient supplies the carrier.  Under an explicit deck
equivariance hypothesis on an existing `ModularFlowData` action, its flow
descends to that quotient and retains the zero and additive flow laws.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinAffineOrbitQuotient

open InfoGeometry.Physics

def descendedRealModularFlow
    (F : ModularFlowData Plane)
    (hdeck : ∀ (t : ℝ) (g : Deck) (p : Plane),
      ∃ h : Deck, F.sigma t (deckAct g p) = deckAct h (F.sigma t p))
    (t : ℝ) : KleinAffineQuotient → KleinAffineQuotient :=
  Quotient.lift
    (fun p => quotientMap (F.sigma t p))
    (by
      intro p q hpq
      obtain ⟨g, rfl⟩ := hpq
      obtain ⟨h, hh⟩ := hdeck t g p
      rw [hh, quotientMap_deckAct])

theorem descendedRealModularFlow_zero
    (F : ModularFlowData Plane)
    (hdeck : ∀ (t : ℝ) (g : Deck) (p : Plane),
      ∃ h : Deck, F.sigma t (deckAct g p) = deckAct h (F.sigma t p))
    (q : KleinAffineQuotient) :
    descendedRealModularFlow F hdeck 0 q = q := by
  induction q using Quotient.inductionOn with
  | h p =>
      change quotientMap (F.sigma 0 p) = quotientMap p
      rw [F.sigma_zero]

theorem descendedRealModularFlow_add
    (F : ModularFlowData Plane)
    (hdeck : ∀ (t : ℝ) (g : Deck) (p : Plane),
      ∃ h : Deck, F.sigma t (deckAct g p) = deckAct h (F.sigma t p))
    (s t : ℝ) (q : KleinAffineQuotient) :
    descendedRealModularFlow F hdeck (s + t) q =
      descendedRealModularFlow F hdeck s
        (descendedRealModularFlow F hdeck t q) := by
  induction q using Quotient.inductionOn with
  | h p =>
      change quotientMap (F.sigma (s + t) p) =
        quotientMap (F.sigma s (F.sigma t p))
      rw [F.sigma_add]

end InfoGeometry.Topology.KleinAffineOrbitQuotient

end noncomputable section

#print axioms InfoGeometry.Topology.KleinAffineOrbitQuotient.descendedRealModularFlow_add
