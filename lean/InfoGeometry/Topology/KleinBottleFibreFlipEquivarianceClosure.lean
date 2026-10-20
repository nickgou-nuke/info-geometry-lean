/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleMappingTorusOrbitBridge

/-!
# Fibre-flip equivariance of the two Klein quotient presentations

The mapping-torus carrier and the literal glide quotient already have a
homeomorphism.  This file supplies the missing equivariance theorem for their
fibre involutions by constructing the involution on the literal quotient from
its torus carrier, rather than treating the action as an informal readout.
-/

noncomputable section
namespace InfoGeometry.Topology.KleinBridgeClosureWave7

open KleinBrillouinBase
open KleinBottleCanonicalCarrier
open KleinBottleOrbitQuotient
open KleinBottleMappingTorusOrbitBridge

private theorem fibreFlip_step_respects {p q : BrillouinTorus}
    (h : glideSetoid p q) :
    glideSetoid (p.1, -p.2) (q.1, -q.2) := by
  rcases h with h | h
  · subst q
    exact Or.inl rfl
  · right
    change (q.1, -q.2) = torusGlide (p.1, -p.2)
    change (q.1, -q.2) = (p.1 + Real.pi, -(-p.2))
    have h₁ : q.1 = p.1 + Real.pi := congrArg Prod.fst h
    have h₂ : q.2 = -p.2 := congrArg Prod.snd h
    rw [h₁, h₂]

private theorem fibreFlip_generated_respects {p q : BrillouinTorus}
    (h : glideSetoid p q) :
    Quotient.mk' (s := glideSetoid) (p.1, -p.2) =
      Quotient.mk' (s := glideSetoid) (q.1, -q.2) := by
  exact Quotient.sound (fibreFlip_step_respects h)

/-- The fibre involution induced on the literal glide quotient. -/
def orbitFibreFlip : KleinBrillouinQuotient ≃ KleinBrillouinQuotient where
  toFun := Quotient.lift
    (fun p : BrillouinTorus => Quotient.mk' (s := glideSetoid) (p.1, -p.2))
    (by intro p q h; exact fibreFlip_generated_respects h)
  invFun := Quotient.lift
    (fun p : BrillouinTorus => Quotient.mk' (s := glideSetoid) (p.1, -p.2))
    (by intro p q h; exact fibreFlip_generated_respects h)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change Quotient.mk' (s := glideSetoid) (p.1, -(-p.2)) = Quotient.mk' (s := glideSetoid) p
    simp
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change Quotient.mk' (s := glideSetoid) (p.1, -(-p.2)) = Quotient.mk' (s := glideSetoid) p
    simp

/-- The quotient fibre flip is continuous for the quotient topology. -/
theorem orbitFibreFlip_continuous :
    Continuous (orbitFibreFlip : KleinBrillouinQuotient → KleinBrillouinQuotient) := by
  apply Continuous.quotient_lift
  exact quotientMap_continuous.comp
    (continuous_fst.prodMk continuous_snd.neg)

/-- The mapping-torus/orbit homeomorphism intertwines the fibre flips. -/
theorem canonicalToOrbit_fibreFlip_equivariant
    (q : CanonicalKleinBottle) :
    canonicalToOrbit (canonicalFibreFlip q) =
      orbitFibreFlip (canonicalToOrbit q) := by
  refine Quotient.inductionOn q ?_
  intro p
  change quotientMap (stripToOrbitRepresentative (p.1, fibreNeg p.2)) =
    orbitFibreFlip (quotientMap (stripToOrbitRepresentative p))
  change quotientMap (stripToOrbitRepresentative (p.1, fibreNeg p.2)) =
    quotientMap (stripToOrbitRepresentative (p.1, fibreNeg p.2))
  rfl

end InfoGeometry.Topology.KleinBridgeClosureWave7
end noncomputable section
