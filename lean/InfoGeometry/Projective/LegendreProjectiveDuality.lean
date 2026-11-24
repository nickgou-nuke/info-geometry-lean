/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.MobiusDual
import InfoGeometry.Algebra.HessianThermodynamicManifold

/-!
# Legendre contact term as a projective point–line pairing

Closing lemma for the projective (L1) lane.  Retrieved context
(Barbaresco, *Entropy 2014*, "Legendre Duality and Projective Duality";
authority `retrieval_context_only`, never proof evidence) pairs the Legendre
dual coordinates `θ, η` with the projective point/line duality and states that
the dual potentials are related by a Legendre transform.

The repository already owns:
* the finite projective point/line pairing and its `SL2` contragredient
  invariance (`Projective.MobiusDual.contragredient_pairing_invariant`, closure
  ledger D17), and
* the `FenchelDualPair` Legendre identity
  (`Algebra.HessianThermodynamicManifold.FenchelDualPair.legendre_identity`).

This module connects them: the Legendre contact term `ψ x + ψ*(∇ψ x)` is
*exactly* the projective pairing of the point `θ = x` with the dual line
`η = ∇ψ x`, and is therefore invariant under the projective contragredient
action.  No claim beyond the stated finite pairing is made.
-/

noncomputable section

namespace InfoGeometry.Projective.LegendreProjectiveDuality

open InfoGeometry.Projective.MobiusDual
open InfoGeometry.Algebra.HessianThermodynamicManifold

/-- The projective point carried by a scalar primal coordinate. -/
def primalPoint (x : ℝ) : ProjectivePoint ℝ :=
  !![x; 0]

/-- The projective line carried by a scalar dual coordinate. -/
def dualLine (η : ℝ) : ProjectiveLine ℝ :=
  !![η, 0]

/-- The projective pairing of the dual line and primal point is the scalar
product `η * x`. -/
@[simp] theorem pairing_dualLine_primalPoint (η x : ℝ) :
    pairing (dualLine η) (primalPoint x) = η * x := by
  simp [pairing, dualLine, primalPoint]

/-- The Legendre contact term equals the projective pairing at dual
coordinates: `⟨∇ψ x, x⟩ = pairing (dualLine (∇ψ x)) (primalPoint x)`. -/
theorem legendre_contact_eq_pairing
    (ψ ψstar : ℝ → ℝ) (grad : ℝ → ℝ)
    (pair : FenchelDualPair ψ ψstar grad) (x : ℝ) :
    ψ x + ψstar (grad x) = pairing (dualLine (grad x)) (primalPoint x) := by
  rw [pair.legendre_identity x]
  simp [pairing, dualLine, primalPoint, InnerSpace.inner]

/-- The Legendre contact term is invariant under the projective contragredient
action on the dual point/line pair.  This is the projective-duality half of the
Legendre–projective bridge. -/
theorem legendre_contact_contragredient_invariant
    (ψ ψstar : ℝ → ℝ) (grad : ℝ → ℝ)
    (pair : FenchelDualPair ψ ψstar grad) (A : SL2 ℝ) (x : ℝ) :
    pairing (actLine A (dualLine (grad x))) (actPoint A (primalPoint x)) =
      ψ x + ψstar (grad x) := by
  rw [contragredient_pairing_invariant]
  exact (legendre_contact_eq_pairing ψ ψstar grad pair x).symm

end InfoGeometry.Projective.LegendreProjectiveDuality
