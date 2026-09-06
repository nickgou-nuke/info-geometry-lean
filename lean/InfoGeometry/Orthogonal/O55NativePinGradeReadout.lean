import InfoGeometry.Orthogonal.O55WittNullFrame
import InfoGeometry.Clifford.Cl55RealSplitPinNullPairProjective

/-!
# Native split-Pin and contact-grade readouts

The native Clifford carrier and the finite contact carrier are deliberately
kept distinct.  This file records the common involutive readouts that are
actually available: a real split-Pin generator exchanges the two projective
null points, while the contact multigrade operation reverses its integer
degree and exchanges the Witt sheet.  No unproved intertwiner is introduced.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence

def crosscapIndex : Fin 5 := 4

theorem native_pin_null_pair_swap :
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nPairProjective crosscapIndex) =
      nbarPairProjective crosscapIndex := by
  exact realSplitPinNullAction_fNegRealPin_nPairProjective crosscapIndex

theorem native_pin_null_pair_swap_back :
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nbarPairProjective crosscapIndex) =
      nPairProjective crosscapIndex := by
  exact realSplitPinNullAction_fNegRealPin_nbarPairProjective crosscapIndex

theorem contact_grade_opposite_involution (d : FullMultiGrade) :
    d.opposite.opposite = d := by
  exact FullMultiGrade.opposite_opposite d

theorem contact_sheet_opposite_involution (q : WittSheetLabel) :
    q.swap.swap = q := by
  exact WittSheetLabel.swap_swap q

theorem native_pin_contact_readout_packet (d : FullMultiGrade)
    (q : WittSheetLabel) :
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nPairProjective crosscapIndex) =
      nbarPairProjective crosscapIndex ∧
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nbarPairProjective crosscapIndex) =
      nPairProjective crosscapIndex ∧
    d.opposite.opposite = d ∧
    q.swap.swap = q := by
  exact ⟨native_pin_null_pair_swap,
    native_pin_null_pair_swap_back,
    contact_grade_opposite_involution d,
    contact_sheet_opposite_involution q⟩

end InfoGeometry.Orthogonal.O55Contact

end noncomputable section
