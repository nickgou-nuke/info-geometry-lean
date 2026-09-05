import InfoGeometry.Orthogonal.O55TwoBoundaryMultigradedReadout
import InfoGeometry.Orthogonal.O55WittCoordinateEquiv
import proofs.PinO55GlideReflection

/-!
# Bridge to the existing `Pin(5,5)` and Klein-glide owners

The repository already owns a native split-Pin reflection, its action on the
canonical null pair, the orientation character of the Klein glide, and the
45-generator `O(5,5)` count.  This file relates those readouts to the new
`D₅` multigrading without identifying the affine glide with the internal Witt
sheet exchange.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55ExistingBridge

open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt
open InfoGeometry.Orthogonal.O55TwoBoundary

/-- The new `1+12+19+12+1` decomposition agrees with the existing total
`O(5,5)` generator count. -/
theorem contact_grade_count_agrees_with_existing_o55 :
    contactGradeDimension (-2) + contactGradeDimension (-1) +
        contactGradeDimension 0 + contactGradeDimension 1 +
          contactGradeDimension 2 =
      PinO55GlideReflection.o55GeneratorCount := by
  calc
    contactGradeDimension (-2) + contactGradeDimension (-1) +
        contactGradeDimension 0 + contactGradeDimension 1 +
          contactGradeDimension 2 = 45 :=
      contact_five_grade_total_dimension
    _ = PinO55GlideReflection.o55GeneratorCount :=
      PinO55GlideReflection.o55_glide_counts.2.1.symm

/-- The existing doubled carrier dimension agrees with the present Witt
indexing by two copies of five axes. -/
theorem witt_index_card_agrees_with_existing_o55 :
    Fintype.card Index = PinO55GlideReflection.o55CarrierDimension := by
  calc
    Fintype.card Index = 10 := by native_decide
    _ = PinO55GlideReflection.o55CarrierDimension :=
      PinO55GlideReflection.o55_glide_counts.1.symm

/-- Existing Pin action on the distinguished projective null pair. -/
theorem existing_pin_crosscap_null_pair_packet :
    InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence.realSplitPinNullAction
        (InfoGeometry.Clifford.Clifford55.fNegRealPin
          PinO55GlideReflection.crosscapIndex)
        (InfoGeometry.Clifford.Clifford55.nPairProjective
          PinO55GlideReflection.crosscapIndex) =
      InfoGeometry.Clifford.Clifford55.nbarPairProjective
        PinO55GlideReflection.crosscapIndex ∧
    InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence.realSplitPinNullAction
        (InfoGeometry.Clifford.Clifford55.fNegRealPin
          PinO55GlideReflection.crosscapIndex)
        (InfoGeometry.Clifford.Clifford55.nbarPairProjective
          PinO55GlideReflection.crosscapIndex) =
      InfoGeometry.Clifford.Clifford55.nPairProjective
        PinO55GlideReflection.crosscapIndex := by
  exact ⟨PinO55GlideReflection.native_crosscap_projective_n_to_nbar,
    PinO55GlideReflection.native_crosscap_projective_nbar_to_n⟩

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
  exact ⟨by native_decide,
    contactGradeDimension_neg_two,
    contactGradeDimension_neg_one,
    contactGradeDimension_zero,
    contactGradeDimension_one,
    contactGradeDimension_two,
    PinO55GlideReflection.o55_glide_counts.2.1,
    PinO55GlideReflection.crosscap_orientation_reversing⟩

end InfoGeometry.Orthogonal.O55ExistingBridge

end noncomputable section
