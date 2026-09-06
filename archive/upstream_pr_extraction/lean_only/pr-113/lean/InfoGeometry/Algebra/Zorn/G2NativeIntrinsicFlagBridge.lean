import InfoGeometry.Algebra.Zorn.G2NativeFlagCardinality
import InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
import InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport
import Mathlib.Data.Fintype.EquivFin

/-!
# Conditional cardinality bridge for intrinsic full flags

This owner avoids overclaiming a canonical identification of native and
intrinsic flags. Downstream consumers that already possess an honest intrinsic
189-cardinality proof may convert that census fact into an abstract finite
carrier equivalence.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeIntrinsicFlagBridge

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport

noncomputable instance intrinsicFlagSigmaFintype :
    Fintype (Σ p : OctImIsotropicPoint, IntrinsicLine p) := by
  classical
  infer_instance

theorem nativeFlag_card_eq_intrinsicFlagSigma_card_of_card189
    (hflag : Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189) :
    Fintype.card NativeFlag = Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) := by
  rw [InfoGeometry.Algebra.Zorn.G2NativeFlagCardinality.nativeFlag_card, hflag]

noncomputable def nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189
    (hflag : Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189) :
    NativeFlag ≃ (Σ p : OctImIsotropicPoint, IntrinsicLine p) :=
  Fintype.equivOfCardEq
    (nativeFlag_card_eq_intrinsicFlagSigma_card_of_card189 hflag)

theorem nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189_surjective
    (hflag : Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189) :
    Function.Surjective
      (nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189 hflag :
        NativeFlag → (Σ p : OctImIsotropicPoint, IntrinsicLine p)) :=
  (nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189 hflag).surjective

end InfoGeometry.Algebra.Zorn.G2NativeIntrinsicFlagBridge
