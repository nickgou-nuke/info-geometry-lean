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

end InfoGeometry.Topology.KleinBottleCanonicalCarrier
end noncomputable section
