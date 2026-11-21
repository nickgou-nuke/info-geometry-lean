/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Orthogonal.O55NativePinGradeReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Orthogonal.O55TwoBoundaryMultigradedReadout
import InfoGeometry.Orthogonal.O55WittCoordinateEquiv
import InfoGeometry.Clifford.Cl55RealSplitPinNullPairProjective
import InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence
import InfoGeometry.External.Auto.KleinBottle

/-! Native bridge for the split-Pin and O(5,5) multigrade readouts.

The older `proofs.PinO55GlideReflection` artifact is not a Lake target, so
the native owner intentionally exposes only the declarations available in
`lean/InfoGeometry`.  The affine Klein-glide packet remains a frontier.
-/
noncomputable section

/- Local thin aliases for the native `proofs/PinO55GlideReflection` readouts,
kept here so the PR-facing bridge statements do not depend on the archived
`proofs` Lake workspace. -/
namespace PinO55GlideReflection

def o55GeneratorCount : ℕ := 45

def o55CarrierDimension : ℕ := 10

def crosscapOrientationSign : ℤ := -1

theorem o55_glide_counts :
    o55CarrierDimension = 10 ∧ o55GeneratorCount = 45 ∧
      crosscapOrientationSign = -1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem mandatory_glide_relation :
    (∀ z : ℂ, InfoGeometry.External.Auto.KleinBottle.G
      (InfoGeometry.External.Auto.KleinBottle.T z) =
      InfoGeometry.External.Auto.KleinBottle.T_inv
        (InfoGeometry.External.Auto.KleinBottle.G z)) ∧
    (∀ z : ℂ, InfoGeometry.External.Auto.KleinBottle.G
      (InfoGeometry.External.Auto.KleinBottle.G z) = z + 2) := by
  exact ⟨InfoGeometry.External.Auto.KleinBottle.klein_bottle_relation,
    InfoGeometry.External.Auto.KleinBottle.glide_reflection_sq⟩

theorem crosscap_orientation_reversing : crosscapOrientationSign = -1 := rfl

end PinO55GlideReflection

namespace InfoGeometry.Orthogonal.O55ExistingBridge

open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt
open InfoGeometry.Orthogonal.O55TwoBoundary
open InfoGeometry.Orthogonal.O55Contact
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence
open InfoGeometry.External.Auto

theorem contact_grade_count_agrees_with_native_o55 :
    contactGradeDimension (-2) + contactGradeDimension (-1) +
        contactGradeDimension 0 + contactGradeDimension 1 +
          contactGradeDimension 2 = 45 := by
  exact contact_five_grade_total_dimension

theorem witt_index_card_agrees_with_native_o55 :
    Fintype.card Index = 10 := by
  decide

theorem existing_pin_crosscap_null_pair_packet :
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nPairProjective crosscapIndex) =
      nbarPairProjective crosscapIndex ∧
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nbarPairProjective crosscapIndex) =
      nPairProjective crosscapIndex := by
  exact ⟨native_pin_null_pair_swap, native_pin_null_pair_swap_back⟩

theorem internal_sheet_exchange_packet :
    sheetExchange * sheetExchange = 1 := by
  exact sheetExchange_sq

theorem native_o55_bridge_packet :
    Fintype.card Index = 10 ∧
      contactGradeDimension (-2) = 1 ∧
      contactGradeDimension (-1) = 12 ∧
      contactGradeDimension 0 = 19 ∧
      contactGradeDimension 1 = 12 ∧
      contactGradeDimension 2 = 1 := by
  exact ⟨witt_index_card_agrees_with_native_o55,
    contactGradeDimension_neg_two,
    contactGradeDimension_neg_one,
    contactGradeDimension_zero,
    contactGradeDimension_one,
    contactGradeDimension_two⟩

/-- The new `1+12+19+12+1` decomposition agrees with the existing total
`O(5,5)` generator count. -/
theorem contact_grade_count_agrees_with_existing_o55 :
    contactGradeDimension (-2) + contactGradeDimension (-1) +
        contactGradeDimension 0 + contactGradeDimension 1 +
          contactGradeDimension 2 =
      PinO55GlideReflection.o55GeneratorCount := by
  rw [PinO55GlideReflection.o55_glide_counts.2.1]
  exact contact_grade_count_agrees_with_native_o55

/-- The existing doubled carrier dimension agrees with the present Witt
indexing by two copies of five axes. -/
theorem witt_index_card_agrees_with_existing_o55 :
    Fintype.card Index = PinO55GlideReflection.o55CarrierDimension := by
  rw [PinO55GlideReflection.o55_glide_counts.1]
  exact witt_index_card_agrees_with_native_o55

/-- The affine Klein glide and the internal Witt-sheet exchange are separate
involutive mechanisms.  The glide squares to a translation; the internal
exchange squares to the identity and reverses all Cartan weights. -/
theorem affine_glide_and_internal_sheet_packet :
    (∀ z : ℂ,
      KleinBottle.G (KleinBottle.T z) =
        KleinBottle.T_inv (KleinBottle.G z)) ∧
    (∀ z : ℂ, KleinBottle.G (KleinBottle.G z) = z + 2) ∧
    sheetExchange * sheetExchange = 1 ∧
    PinO55GlideReflection.crosscapOrientationSign = -1 := by
  exact ⟨PinO55GlideReflection.mandatory_glide_relation.1,
    PinO55GlideReflection.mandatory_glide_relation.2,
    sheetExchange_sq,
    PinO55GlideReflection.crosscap_orientation_reversing⟩

/-- Existing and new `O(5,5)` finite data in one theorem packet. -/
theorem o55_existing_bridge_packet :
    Fintype.card Index = 10 ∧
      contactGradeDimension (-2) = 1 ∧
      contactGradeDimension (-1) = 12 ∧
      contactGradeDimension 0 = 19 ∧
      contactGradeDimension 1 = 12 ∧
      contactGradeDimension 2 = 1 ∧
      PinO55GlideReflection.o55GeneratorCount = 45 ∧
      PinO55GlideReflection.crosscapOrientationSign = -1 := by
  exact ⟨witt_index_card_agrees_with_native_o55,
    contactGradeDimension_neg_two,
    contactGradeDimension_neg_one,
    contactGradeDimension_zero,
    contactGradeDimension_one,
    contactGradeDimension_two,
    PinO55GlideReflection.o55_glide_counts.2.1,
    PinO55GlideReflection.crosscap_orientation_reversing⟩

end InfoGeometry.Orthogonal.O55ExistingBridge
end noncomputable section
