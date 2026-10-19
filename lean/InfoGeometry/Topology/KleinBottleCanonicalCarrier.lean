/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.CompactMappingTorusGluing
import InfoGeometry.Topology.KleinBrillouinBase

/-!
# Canonical compact mapping-torus carrier for the Klein gluing

The carrier is the compact interval mapping torus of fibre negation.  The
quotient projection and the induced fibre flip are defined by `Quotient.lift`;
no identification with the independent torus-orbit quotient is asserted here.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCanonicalCarrier

open KleinBrillouinBase
open InfoGeometry.Topology.CompactMappingTorus

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def fibreNeg : MomentumCircle → MomentumCircle := Neg.neg

abbrev CanonicalKleinBottle : Type :=
  Carrier fibreNeg

def canonicalMk : Base × MomentumCircle → CanonicalKleinBottle :=
  project fibreNeg

@[simp] theorem canonical_endpoint (x : MomentumCircle) :
    canonicalMk (⟨0, by constructor <;> norm_num⟩, x) =
      canonicalMk (⟨1, by constructor <;> norm_num⟩, fibreNeg x) := by
  exact project_endpoint fibreNeg x

private theorem fibreFlip_step_respects {p q : Base × MomentumCircle}
    (h : endpointStep fibreNeg p q) :
    endpointStep fibreNeg (p.1, fibreNeg p.2) (q.1, fibreNeg q.2) := by
  rcases h with h | h
  · left
    exact ⟨h.1, h.2.1, by
      simpa [fibreNeg] using congrArg fibreNeg h.2.2⟩
  · right
    exact ⟨h.1, h.2.1, by
      simpa [fibreNeg] using congrArg fibreNeg h.2.2⟩

private theorem fibreFlip_respects : ∀ {p q : Base × MomentumCircle},
    Relation.EqvGen (endpointStep fibreNeg) p q →
      Relation.EqvGen (endpointStep fibreNeg)
        (p.1, fibreNeg p.2) (q.1, fibreNeg q.2) := by
  intro p q h
  induction h with
  | rel p q h => exact Relation.EqvGen.rel _ _ (fibreFlip_step_respects h)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q r _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def fibreFlipMap : CanonicalKleinBottle → CanonicalKleinBottle :=
  @Quotient.lift (Base × MomentumCircle) CanonicalKleinBottle
    (endpointSetoid fibreNeg)
    (fun p => @Quotient.mk (Base × MomentumCircle) (endpointSetoid fibreNeg)
      (p.1, fibreNeg p.2))
    (by
      intro p q h
      exact Quotient.sound (fibreFlip_respects h))

def canonicalFibreFlip : CanonicalKleinBottle ≃ CanonicalKleinBottle where
  toFun := fibreFlipMap
  invFun := fibreFlipMap
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change @Quotient.mk (Base × MomentumCircle) (endpointSetoid fibreNeg)
      (p.1, fibreNeg (fibreNeg p.2)) = @Quotient.mk _ _ p
    simp [fibreNeg]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change @Quotient.mk (Base × MomentumCircle) (endpointSetoid fibreNeg)
      (p.1, fibreNeg (fibreNeg p.2)) = @Quotient.mk _ _ p
    simp [fibreNeg]

@[simp] theorem canonicalFibreFlip_apply (p : Base × MomentumCircle) :
    canonicalFibreFlip (canonicalMk p) = canonicalMk (p.1, fibreNeg p.2) := by
  change fibreFlipMap (project fibreNeg p) = project fibreNeg (p.1, fibreNeg p.2)
  simp [fibreFlipMap, project]

 theorem canonicalFibreFlip_involutive (q : CanonicalKleinBottle) :
    canonicalFibreFlip (canonicalFibreFlip q) = q := by
  exact canonicalFibreFlip.left_inv q

end InfoGeometry.Topology.KleinBottleCanonicalCarrier

end noncomputable section
