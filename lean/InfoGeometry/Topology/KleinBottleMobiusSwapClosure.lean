/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleCanonicalCarrier

/-!
# Section 152: double-swap closure for the Möbius-band pushout

This file adds the actual involution of the native `TopCat` pushout obtained by
swapping its two identical Möbius-band summands.  It uses the existing
Möbius-band carrier and pushout, and proves the action on both coprojections
and its square by the pushout universal property.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCanonicalCarrier

open CategoryTheory CategoryTheory.Limits

open KleinBottleCanonicalCarrier
open KleinBrillouinBase
open InfoGeometry.Topology.CompactMappingTorus

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem swap_boundary_condition :
    boundaryToBandHom ≫ mobiusGluedInr =
      boundaryToBandHom ≫ mobiusGluedInl := by
  rw [mobiusGlued_boundary_condition]

/-- The involution exchanging the two Möbius-band summands in the native
`TopCat` pushout. -/
def mobiusGluedSwap : MobiusGluedObj ⟶ MobiusGluedObj :=
  pushout.desc mobiusGluedInr mobiusGluedInl swap_boundary_condition

@[simp] theorem mobiusGluedInl_comp_swap :
    mobiusGluedInl ≫ mobiusGluedSwap = mobiusGluedInr := by
  exact pushout.inl_desc mobiusGluedInr mobiusGluedInl swap_boundary_condition

@[simp] theorem mobiusGluedInr_comp_swap :
    mobiusGluedInr ≫ mobiusGluedSwap = mobiusGluedInl := by
  exact pushout.inr_desc mobiusGluedInr mobiusGluedInl swap_boundary_condition

/-- Swapping the two Möbius summands twice is the identity morphism. -/
theorem mobiusGluedSwap_sq :
    mobiusGluedSwap ≫ mobiusGluedSwap = 𝟙 MobiusGluedObj := by
  apply pushout.hom_ext
  · calc
      mobiusGluedInl ≫ (mobiusGluedSwap ≫ mobiusGluedSwap) =
          (mobiusGluedInl ≫ mobiusGluedSwap) ≫ mobiusGluedSwap := by
            rw [Category.assoc]
      _ = mobiusGluedInr ≫ mobiusGluedSwap := by
            rw [mobiusGluedInl_comp_swap]
      _ = mobiusGluedInl := mobiusGluedInr_comp_swap
      _ = mobiusGluedInl ≫ 𝟙 MobiusGluedObj := by rw [Category.comp_id]
  · calc
      mobiusGluedInr ≫ (mobiusGluedSwap ≫ mobiusGluedSwap) =
          (mobiusGluedInr ≫ mobiusGluedSwap) ≫ mobiusGluedSwap := by
            rw [Category.assoc]
      _ = mobiusGluedInl ≫ mobiusGluedSwap := by
            rw [mobiusGluedInr_comp_swap]
      _ = mobiusGluedInr := mobiusGluedInl_comp_swap
      _ = mobiusGluedInr ≫ 𝟙 MobiusGluedObj := by rw [Category.comp_id]

/-- Reflection across the midpoint of the circle fibre exchanges the two
semicircles used to realize the two Möbius-band summands. -/
def semicircleReflection (x : MomentumCircle) : MomentumCircle :=
  (Real.pi : MomentumCircle) - x

theorem semicircleReflection_involutive (x : MomentumCircle) :
    semicircleReflection (semicircleReflection x) = x := by
  simp [semicircleReflection]

theorem semicircleReflection_commutes_neg (x : MomentumCircle) :
    semicircleReflection (-x) = -semicircleReflection x := by
  have hpi : (-Real.pi : MomentumCircle) = Real.pi := by
    exact (eq_neg_of_add_eq_zero_left KleinBrillouinBase.pi_add_pi_eq_zero).symm
  calc
    semicircleReflection (-x) = (Real.pi : MomentumCircle) + x := by
      simp [semicircleReflection]
    _ = x + (Real.pi : MomentumCircle) := add_comm _ _
    _ = -semicircleReflection x := by
      rw [semicircleReflection, sub_eq_add_neg, neg_add, hpi]
      simpa using add_comm x (Real.pi : MomentumCircle)

theorem semicircleReflection_continuous :
    Continuous (semicircleReflection : MomentumCircle → MomentumCircle) := by
  have hconst : Continuous (fun _ : MomentumCircle => (Real.pi : MomentumCircle)) :=
    continuous_const
  change Continuous (fun x : MomentumCircle => (Real.pi : MomentumCircle) - x)
  exact hconst.sub continuous_id

def semicircleReflectionHomeomorph : MomentumCircle ≃ₜ MomentumCircle where
  toEquiv :=
    { toFun := semicircleReflection
      invFun := semicircleReflection
      left_inv := semicircleReflection_involutive
      right_inv := semicircleReflection_involutive }
  continuous_toFun := semicircleReflection_continuous
  continuous_invFun := semicircleReflection_continuous

/-- The circle reflection descends through the mapping-torus relation to an
involution of the canonical Klein-bottle carrier. -/
def canonicalSemicircleReflection : CanonicalKleinBottle ≃ₜ CanonicalKleinBottle :=
  CompactMappingTorus.homeomorphOfConjugacy
    semicircleReflectionHomeomorph
    semicircleReflection_commutes_neg

@[simp] theorem canonicalSemicircleReflection_apply (t : Base) (x : MomentumCircle) :
    canonicalSemicircleReflection (canonicalMk (t, x)) =
      canonicalMk (t, semicircleReflection x) := by
  rfl

theorem canonicalSemicircleReflection_involutive (x : CanonicalKleinBottle) :
    canonicalSemicircleReflection (canonicalSemicircleReflection x) = x := by
  refine Quotient.inductionOn x ?_
  intro p
  change canonicalMk
      (p.1, semicircleReflection (semicircleReflection p.2)) =
    canonicalMk (p.1, p.2)
  rw [semicircleReflection_involutive]

theorem semicircleReflection_leftArc (x : MobiusInterval) :
    semicircleReflection (mobiusLeftArc x) = mobiusRightArc x := by
  change ((Real.pi - (Real.pi * x.1 + Real.pi / 2) : ℝ) : MomentumCircle) =
    ((Real.pi / 2 - Real.pi * x.1 : ℝ) : MomentumCircle)
  congr 1
  ring

theorem canonicalSemicircleReflection_leftBandMap (x : MobiusBand) :
    canonicalSemicircleReflection (mobiusLeftBandMap x) = mobiusRightBandMap x := by
  refine Quotient.inductionOn x ?_
  intro p
  change canonicalSemicircleReflection
      (canonicalMk (p.1, mobiusLeftArc p.2)) =
    canonicalMk (p.1, mobiusRightArc p.2)
  rw [canonicalSemicircleReflection_apply, semicircleReflection_leftArc]

/-- The swap of the Möbius-band summands is carried to the explicit fibre
reflection on the mapping-torus Klein bottle by the gluing map. -/
theorem mobiusGluedSwap_intertwines_semicircleReflection :
    mobiusGluedSwap ≫ mobiusGluedToCanonical =
      mobiusGluedToCanonical ≫
        TopCat.ofHom ⟨canonicalSemicircleReflection,
          canonicalSemicircleReflection.continuous⟩ := by
  apply pushout.hom_ext
  · calc
      mobiusGluedInl ≫ (mobiusGluedSwap ≫ mobiusGluedToCanonical) =
          (mobiusGluedInl ≫ mobiusGluedSwap) ≫ mobiusGluedToCanonical := by
            rw [Category.assoc]
      _ = mobiusGluedInr ≫ mobiusGluedToCanonical := by
            rw [mobiusGluedInl_comp_swap]
      _ = TopCat.ofHom ⟨mobiusRightBandMap, mobiusRightBandMap_continuous⟩ :=
            mobiusGluedInr_comp_mobiusGluedToCanonical
      _ = TopCat.ofHom ⟨mobiusLeftBandMap, mobiusLeftBandMap_continuous⟩ ≫
          TopCat.ofHom ⟨canonicalSemicircleReflection,
            canonicalSemicircleReflection.continuous⟩ := by
            apply TopCat.hom_ext
            apply ContinuousMap.ext
            intro x
            change mobiusRightBandMap x =
              canonicalSemicircleReflection (mobiusLeftBandMap x)
            exact (canonicalSemicircleReflection_leftBandMap x).symm
      _ = mobiusGluedInl ≫
          (mobiusGluedToCanonical ≫
            TopCat.ofHom ⟨canonicalSemicircleReflection,
              canonicalSemicircleReflection.continuous⟩) := by
            calc
              _ = (mobiusGluedInl ≫ mobiusGluedToCanonical) ≫
                  TopCat.ofHom ⟨canonicalSemicircleReflection,
                    canonicalSemicircleReflection.continuous⟩ := by
                    exact (congrArg (fun f : MobiusBandObj ⟶ TopCat.of CanonicalKleinBottle =>
                      f ≫ TopCat.ofHom ⟨canonicalSemicircleReflection,
                        canonicalSemicircleReflection.continuous⟩)
                      mobiusGluedInl_comp_mobiusGluedToCanonical).symm
              _ = mobiusGluedInl ≫
                  (mobiusGluedToCanonical ≫
                    TopCat.ofHom ⟨canonicalSemicircleReflection,
                      canonicalSemicircleReflection.continuous⟩) := by
                    rw [Category.assoc]
  · calc
      mobiusGluedInr ≫ (mobiusGluedSwap ≫ mobiusGluedToCanonical) =
          (mobiusGluedInr ≫ mobiusGluedSwap) ≫ mobiusGluedToCanonical := by
            rw [Category.assoc]
      _ = mobiusGluedInl ≫ mobiusGluedToCanonical := by
            rw [mobiusGluedInr_comp_swap]
      _ = TopCat.ofHom ⟨mobiusLeftBandMap, mobiusLeftBandMap_continuous⟩ :=
            mobiusGluedInl_comp_mobiusGluedToCanonical
      _ = TopCat.ofHom ⟨mobiusRightBandMap, mobiusRightBandMap_continuous⟩ ≫
          TopCat.ofHom ⟨canonicalSemicircleReflection,
            canonicalSemicircleReflection.continuous⟩ := by
            apply TopCat.hom_ext
            apply ContinuousMap.ext
            intro x
            change mobiusLeftBandMap x =
              canonicalSemicircleReflection (mobiusRightBandMap x)
            have h := canonicalSemicircleReflection_leftBandMap x
            calc
              mobiusLeftBandMap x =
                  canonicalSemicircleReflection
                    (canonicalSemicircleReflection (mobiusLeftBandMap x)) := by
                      exact (canonicalSemicircleReflection_involutive _).symm
              _ = canonicalSemicircleReflection (mobiusRightBandMap x) := by rw [h]
      _ = mobiusGluedInr ≫
          (mobiusGluedToCanonical ≫
            TopCat.ofHom ⟨canonicalSemicircleReflection,
              canonicalSemicircleReflection.continuous⟩) := by
            calc
              _ = (mobiusGluedInr ≫ mobiusGluedToCanonical) ≫
                  TopCat.ofHom ⟨canonicalSemicircleReflection,
                    canonicalSemicircleReflection.continuous⟩ := by
                    exact (congrArg (fun f : MobiusBandObj ⟶ TopCat.of CanonicalKleinBottle =>
                      f ≫ TopCat.ofHom ⟨canonicalSemicircleReflection,
                        canonicalSemicircleReflection.continuous⟩)
                      mobiusGluedInr_comp_mobiusGluedToCanonical).symm
              _ = mobiusGluedInr ≫
                  (mobiusGluedToCanonical ≫
                    TopCat.ofHom ⟨canonicalSemicircleReflection,
                      canonicalSemicircleReflection.continuous⟩) := by
                    rw [Category.assoc]

end InfoGeometry.Topology.KleinBottleCanonicalCarrier
end noncomputable section
