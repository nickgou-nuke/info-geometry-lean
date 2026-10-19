/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.MappingTorusGluing
import InfoGeometry.Topology.KleinBrillouinBase

/-!
# Canonical mapping-torus carrier for the Klein gluing

This file supplies a genuine quotient carrier for the standard Klein gluing.
It deliberately records the mapping-torus presentation separately from the
torus-orbit quotient in `KleinBottleOrbitQuotient`; an equivalence between
those two presentations requires a further quotient comparison theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCanonicalCarrier

open KleinBrillouinBase
open MappingTorusGluing

def fibreNeg : MomentumCircle → MomentumCircle := Neg.neg

theorem fibreNeg_involutive (x : MomentumCircle) :
    fibreNeg (fibreNeg x) = x := by
  simp [fibreNeg]

def fibreGluing : InvolutiveGluing (F := MomentumCircle) where
  map := fibreNeg
  involutive := fibreNeg_involutive

/-- The canonical set-level mapping-torus carrier for the Klein gluing. -/
abbrev CanonicalKleinBottle : Type :=
  InvolutiveGluing.torus fibreGluing

def canonicalMk : ℝ × MomentumCircle → CanonicalKleinBottle :=
  mappingTorusMk fibreNeg

theorem canonical_endpoint (x : MomentumCircle) :
    canonicalMk (0, x) = canonicalMk (1, fibreNeg x) := by
  exact mappingTorus_endpoint fibreNeg x

theorem canonical_endpoint_involutive (x : MomentumCircle) :
    fibreNeg (fibreNeg x) = x :=
  fibreNeg_involutive x

theorem fibreFlip_respects : ∀ ⦃p q : ℝ × MomentumCircle⦄,
    Relation.EqvGen (endpointStep fibreNeg) p q →
      Relation.EqvGen (endpointStep fibreNeg)
        (p.1, fibreNeg p.2) (q.1, fibreNeg q.2) := by
    intro p q hpq
    induction hpq with
    | rel p q h =>
        rcases h with h | h
        · rcases h with ⟨hp0, hq1, hq⟩
          apply Relation.EqvGen.rel
          exact Or.inl ⟨hp0, hq1, by
            change q.2 = -p.2 at hq
            rw [hq]
            simp [fibreNeg, fibreGluing]⟩
        · rcases h with ⟨hp1, hq0, hpq⟩
          apply Relation.EqvGen.rel
          exact Or.inr ⟨hp1, hq0, by
            change p.2 = -q.2 at hpq
            rw [hpq]
            simp [fibreNeg, fibreGluing]⟩
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans p q r _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem fibreFlip_map_respects : ∀ ⦃p q : ℝ × MomentumCircle⦄,
    @Setoid.r (ℝ × MomentumCircle) (endpointRelation fibreNeg) p q →
      @Setoid.r (ℝ × MomentumCircle) (endpointRelation fibreNeg)
        (p.1, fibreNeg p.2) (q.1, fibreNeg q.2) := by
  intro p q h
  exact fibreFlip_respects h

def fibreFlipMap : CanonicalKleinBottle → CanonicalKleinBottle :=
  Quotient.map (fun p : ℝ × MomentumCircle => (p.1, fibreNeg p.2))
    fibreFlip_map_respects

def canonicalFibreFlip : CanonicalKleinBottle ≃ CanonicalKleinBottle where
  toFun := fibreFlipMap
  invFun := fibreFlipMap
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change Quotient.mk _ (p.1, -(-p.2)) = Quotient.mk _ p
    rw [neg_neg]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change Quotient.mk _ (p.1, -(-p.2)) = Quotient.mk _ p
    rw [neg_neg]

theorem canonicalFibreFlip_apply (p : ℝ × MomentumCircle) :
    canonicalFibreFlip (canonicalMk p) = canonicalMk (p.1, fibreNeg p.2) := by
  change fibreFlipMap (Quotient.mk (endpointRelation fibreNeg) p) = _
  exact Quotient.map_mk _ _ _

theorem canonicalFibreFlip_involutive (q : CanonicalKleinBottle) :
    canonicalFibreFlip (canonicalFibreFlip q) = q := by
  exact canonicalFibreFlip.left_inv q

end InfoGeometry.Topology.KleinBottleCanonicalCarrier

end
