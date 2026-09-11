import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Structural bound for the intrinsic base-line fibre

Every intrinsic line through the native base point is determined by its two
other points.  This owner records that reduction without identifying the
intrinsic relation with the older exported native-line carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFiberBounds

open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

abbrev Point :=
  InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint

abbrev BaseNeighborPair (p : Point) :=
  {s : Finset Point //
    s.card = 2 ∧ s ⊆ zornZeroNeighborSet p}

def intrinsicBaseLineErase
    (L : IntrinsicLine
      nativeBaseIsotropicPoint) :
    BaseNeighborPair
      nativeBaseIsotropicPoint :=
  ⟨L.1.erase nativeBaseIsotropicPoint,
    intrinsicLine_erase_card L,
    intrinsicLine_subset_zornZeroNeighborSet L⟩

theorem intrinsicBaseLineErase_injective :
    Function.Injective
      (intrinsicBaseLineErase :
        IntrinsicLine nativeBaseIsotropicPoint →
          BaseNeighborPair nativeBaseIsotropicPoint) := by
  intro L M hLM
  apply intrinsicLine_ext_of_erase_eq
  exact congrArg Subtype.val hLM

theorem intrinsicBaseLine_fibre_le_neighborPairs
    [Fintype (IntrinsicLine nativeBaseIsotropicPoint)]
    [Fintype (BaseNeighborPair nativeBaseIsotropicPoint)] :
    Fintype.card (IntrinsicLine nativeBaseIsotropicPoint) ≤
      Fintype.card (BaseNeighborPair nativeBaseIsotropicPoint) := by
  exact Fintype.card_le_of_injective
    intrinsicBaseLineErase intrinsicBaseLineErase_injective

end InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFiberBounds
