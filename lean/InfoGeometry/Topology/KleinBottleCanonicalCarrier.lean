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

def canonicalFibreFlip : CanonicalKleinBottle ≃ CanonicalKleinBottle where
  toFun := Quotient.lift (fun p : ℝ × MomentumCircle => (p.1, fibreNeg p.2)) (by
    intro p q hpq
    induction hpq with
    | rel p q h =>
        rcases h with h | h
        · rcases h with ⟨hp0, hq1, hq⟩
          apply Relation.EqvGen.rel
          exact Or.inl ⟨hp0, hq1, by simpa [fibreNeg] using congrArg fibreNeg hq⟩
        · rcases h with ⟨hp1, hq0, hpq⟩
          apply Relation.EqvGen.rel
          exact Or.inr ⟨hp1, hq0, by simpa [fibreNeg] using congrArg fibreNeg hpq⟩
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans p q r _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
  invFun := Quotient.lift (fun p : ℝ × MomentumCircle => (p.1, fibreNeg p.2)) (by
    intro p q hpq
    induction hpq with
    | rel p q h =>
        rcases h with h | h
        · rcases h with ⟨hp0, hq1, hq⟩
          apply Relation.EqvGen.rel
          exact Or.inl ⟨hp0, hq1, by simpa [fibreNeg] using congrArg fibreNeg hq⟩
        · rcases h with ⟨hp1, hq0, hpq⟩
          apply Relation.EqvGen.rel
          exact Or.inr ⟨hp1, hq0, by simpa [fibreNeg] using congrArg fibreNeg hpq⟩
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans p q r _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    simp [fibreNeg]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    simp [fibreNeg]

theorem canonicalFibreFlip_apply (p : ℝ × MomentumCircle) :
    canonicalFibreFlip (canonicalMk p) = canonicalMk (p.1, fibreNeg p.2) := by
  rfl

theorem canonicalFibreFlip_involutive (q : CanonicalKleinBottle) :
    canonicalFibreFlip (canonicalFibreFlip q) = q := by
  exact canonicalFibreFlip.left_inv q

end InfoGeometry.Topology.KleinBottleCanonicalCarrier

end
