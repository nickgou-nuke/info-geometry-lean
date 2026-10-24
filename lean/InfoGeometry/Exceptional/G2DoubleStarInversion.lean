/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.G2KleinRootLabelBridge
import InfoGeometry.Exceptional.G2CyclotomicCoordinateActionBridge

/-! # Sheet reversal inverts the native double-star Coxeter action

Reuse the calibrated root carrier and its existing permutation transport.
The commuting square below is an equality of actual permutation maps, not
an editorial dependency diamond. No identification with modular shear units
or topological Klein-bottle monodromy is asserted.
-/
namespace InfoGeometry.Exceptional.G2DoubleStarInversion
open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Exceptional.G2KleinRootLabelBridge
open InfoGeometry.Exceptional.G2CyclotomicCoordinateActionBridge

/-- The two sectors rotate in opposite directions, so exchanging them
reverses the calibrated Coxeter action. -/
theorem sheetFlip_coxeter_inverse :
    cyclotomicSheetFlip * cyclotomicCoxeterPerm * cyclotomicSheetFlip =
      cyclotomicCoxeterPerm⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  apply Equiv.ext
  rintro ⟨b,k⟩
  cases b <;>
    simp [Equiv.Perm.mul_apply,cyclotomicSheetFlip,
      cyclotomicCoxeterPerm,cyclotomicCoxeterFun]

/-- Existing root equivalence transports the sheet exchange exactly. -/
theorem transport_sheetFlip :
    transportRootPerm cyclotomicSheetFlip = kleinRootLabelThroatFlip := by
  apply Equiv.ext
  intro x
  simp [transportRootPerm,Equiv.trans_apply,cyclotomicSheetFlip,
    kleinRootLabelThroatFlip_apply]

/-- Existing root equivalence transports the Coxeter permutation exactly. -/
theorem transport_coxeter : transportRootPerm cyclotomicCoxeterPerm = cRoot := by
  apply Equiv.ext
  intro x
  apply signedRootCyclotomicEquiv.injective
  simp only [transportRootPerm,Equiv.trans_apply,Equiv.apply_symm_apply,
    signedRootCyclotomicEquiv_cRoot]

/-- The diamond: compose on cyclotomic coordinates and then transport,
or transport the factors and compose on native coordinate roots. -/
theorem transport_reversal_square :
    transportRootPerm (cyclotomicSheetFlip * cyclotomicCoxeterPerm) =
      kleinRootLabelThroatFlip * cRoot := by
  rw [transportRootPerm_mul,transport_sheetFlip,transport_coxeter]

/-- Grading reversal inverts the Coxeter action on the actual root carrier. -/
theorem throatFlip_coxeter_inverse :
    kleinRootLabelThroatFlip * cRoot * kleinRootLabelThroatFlip = cRoot⁻¹ := by
  have h := congrArg transportRootPermHom sheetFlip_coxeter_inverse
  simp only [map_mul,map_inv] at h
  change transportRootPerm cyclotomicSheetFlip * transportRootPerm cyclotomicCoxeterPerm *
    transportRootPerm cyclotomicSheetFlip = (transportRootPerm cyclotomicCoxeterPerm)⁻¹ at h
  simpa only [transport_sheetFlip,transport_coxeter] using h

end InfoGeometry.Exceptional.G2DoubleStarInversion
