/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.CompactMappingTorusGluing
import InfoGeometry.Topology.KleinBrillouinBase
import Mathlib.Topology.Category.TopCat.Basic

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
open CategoryTheory CategoryTheory.Limits

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

/-! ## A genuine Möbius-band carrier and its boundary pushout -/

abbrev MobiusInterval := Set.Icc (0 : ℝ) 1

def mobiusFlip (x : MobiusInterval) : MobiusInterval :=
  ⟨1 - x.1, by constructor <;> linarith [x.2.1, x.2.2]⟩

theorem mobiusFlip_involutive (x : MobiusInterval) :
    mobiusFlip (mobiusFlip x) = x := by
  apply Subtype.ext
  dsimp [mobiusFlip]
  ring

abbrev MobiusBand := Carrier mobiusFlip

def mobiusBandMk : Base × MobiusInterval → MobiusBand :=
  project mobiusFlip

theorem mobiusBand_endpoint (x : MobiusInterval) :
    mobiusBandMk (⟨0, by constructor <;> norm_num⟩, x) =
      mobiusBandMk (⟨1, by constructor <;> norm_num⟩, mobiusFlip x) := by
  exact project_endpoint mobiusFlip x

abbrev MobiusBoundaryBit := Bool

def boundaryFlip : MobiusBoundaryBit → MobiusBoundaryBit
  | false => true
  | true => false

theorem boundaryFlip_involutive (b : MobiusBoundaryBit) :
    boundaryFlip (boundaryFlip b) = b := by
  cases b <;> rfl

abbrev MobiusBoundary := Carrier boundaryFlip

def boundaryEndpoint : MobiusBoundaryBit → MobiusInterval
  | false => ⟨0, by constructor <;> norm_num⟩
  | true => ⟨1, by constructor <;> norm_num⟩

theorem boundaryEndpoint_flip (b : MobiusBoundaryBit) :
    boundaryEndpoint (boundaryFlip b) = mobiusFlip (boundaryEndpoint b) := by
  cases b <;> apply Subtype.ext <;>
    simp [boundaryEndpoint, boundaryFlip, mobiusFlip]

private theorem boundaryToBand_respects {p q : Base × MobiusBoundaryBit}
    (hpq : Relation.EqvGen (endpointStep boundaryFlip) p q) :
    mobiusBandMk (p.1, boundaryEndpoint p.2) =
      mobiusBandMk (q.1, boundaryEndpoint q.2) := by
  induction hpq with
  | rel p q h =>
      rcases h with h | h
      · apply Quotient.sound
        exact Relation.EqvGen.rel _ _ (Or.inl ⟨h.1, h.2.1, by
          rw [h.2.2]
          exact boundaryEndpoint_flip p.2⟩)
      · apply Quotient.sound
        exact Relation.EqvGen.rel _ _ (Or.inr ⟨h.1, h.2.1, by
          rw [h.2.2]
          exact boundaryEndpoint_flip q.2⟩)
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def boundaryToBand : MobiusBoundary → MobiusBand :=
  @Quotient.lift (Base × MobiusBoundaryBit) MobiusBand
    (endpointSetoid boundaryFlip)
    (fun p => mobiusBandMk (p.1, boundaryEndpoint p.2))
    (by intro p q hpq; exact boundaryToBand_respects hpq)

theorem boundaryToBand_continuous : Continuous boundaryToBand := by
  apply Continuous.quotient_lift
  · have hboundary : Continuous boundaryEndpoint := continuous_of_discreteTopology
    exact continuous_quotient_mk'.comp
      (continuous_fst.prodMk (hboundary.comp continuous_snd))

abbrev MobiusBandObj : TopCat := TopCat.of MobiusBand
abbrev MobiusBoundaryObj : TopCat := TopCat.of MobiusBoundary

def boundaryToBandHom : MobiusBoundaryObj ⟶ MobiusBandObj :=
  TopCat.ofHom ⟨boundaryToBand, boundaryToBand_continuous⟩

/-! The double is the native TopCat pushout of the two identical boundary maps. -/

abbrev MobiusGluedObj : TopCat :=
  pushout boundaryToBandHom boundaryToBandHom

abbrev MobiusGlued := MobiusGluedObj.carrier

def mobiusGluedInl : MobiusBandObj ⟶ MobiusGluedObj :=
  pushout.inl boundaryToBandHom boundaryToBandHom

def mobiusGluedInr : MobiusBandObj ⟶ MobiusGluedObj :=
  pushout.inr boundaryToBandHom boundaryToBandHom

theorem mobiusGlued_boundary_condition :
    boundaryToBandHom ≫ mobiusGluedInl =
      boundaryToBandHom ≫ mobiusGluedInr := by
  exact pushout.condition

theorem mobiusGlued_hom_ext {Y : TopCat}
    (f g : MobiusGluedObj ⟶ Y)
    (h₁ : mobiusGluedInl ≫ f = mobiusGluedInl ≫ g)
    (h₂ : mobiusGluedInr ≫ f = mobiusGluedInr ≫ g) :
    f = g := by
  exact pushout.hom_ext h₁ h₂

theorem mobiusGlued_desc
    {Y : TopCat}
    (left right : MobiusBandObj ⟶ Y)
    (h : boundaryToBandHom ≫ left = boundaryToBandHom ≫ right) :
    mobiusGluedInl ≫ (pushout.desc left right h) = left := by
  exact pushout.inl_desc left right h

theorem mobiusGlued_desc_right
    {Y : TopCat}
    (left right : MobiusBandObj ⟶ Y)
    (h : boundaryToBandHom ≫ left = boundaryToBandHom ≫ right) :
    mobiusGluedInr ≫ (pushout.desc left right h) = right := by
  exact pushout.inr_desc left right h

end InfoGeometry.Topology.KleinBottleCanonicalCarrier

end noncomputable section
