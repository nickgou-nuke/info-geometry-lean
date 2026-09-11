import InfoGeometry.Orthogonal.O55NativePinGradeReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Orthogonal.O55TwoBoundaryMultigradedReadout
import InfoGeometry.Orthogonal.O55WittCoordinateEquiv
import InfoGeometry.Clifford.Cl55RealSplitPinNullPairProjective
import InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence

/-! Native bridge for the split-Pin and O(5,5) multigrade readouts.

The older `proofs.PinO55GlideReflection` artifact is not a Lake target, so
the native owner intentionally exposes only the declarations available in
`lean/InfoGeometry`.  The affine Klein-glide packet remains a frontier.
-/
noncomputable section
namespace InfoGeometry.Orthogonal.O55ExistingBridge

open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt
open InfoGeometry.Orthogonal.O55TwoBoundary
open InfoGeometry.Orthogonal.O55Contact
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence

theorem contact_grade_count_agrees_with_native_o55 :
    contactGradeDimension (-2) + contactGradeDimension (-1) +
        contactGradeDimension 0 + contactGradeDimension 1 +
          contactGradeDimension 2 = 45 := by
  exact contact_five_grade_total_dimension

theorem witt_index_card_agrees_with_native_o55 :
    Fintype.card Index = 10 := by
  native_decide

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

end InfoGeometry.Orthogonal.O55ExistingBridge
end noncomputable section
