import InfoGeometry.Orthogonal.O55WittNullFrame
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55RealSplitPinNullPairProjective

/-!
# Native contact/Pin readouts

This owner deliberately uses the native `InfoGeometry` carriers.  The former
version imported `proofs.PinO55GlideReflection`, which is not a Lake target and
therefore could not be part of the verified source graph.  The affine Klein
glide is a separate frontier; the theorems below retain the proved finite
content: dimension counts, projective null-sheet exchange, and involutive
contact/sheet opposition.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence

theorem matrix_clifford_count_agreement :
    Fintype.card (Fin 10) = 10 ∧ Nat.choose 10 2 = 45 := by
  decide

theorem pin_crosscap_projective_null_swap :
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nPairProjective crosscapIndex) =
      nbarPairProjective crosscapIndex ∧
    realSplitPinNullAction
        (fNegRealPin crosscapIndex)
        (nbarPairProjective crosscapIndex) =
      nPairProjective crosscapIndex := by
  exact ⟨realSplitPinNullAction_fNegRealPin_nPairProjective crosscapIndex,
    realSplitPinNullAction_fNegRealPin_nbarPairProjective crosscapIndex⟩

end InfoGeometry.Orthogonal.O55Contact

end noncomputable section
