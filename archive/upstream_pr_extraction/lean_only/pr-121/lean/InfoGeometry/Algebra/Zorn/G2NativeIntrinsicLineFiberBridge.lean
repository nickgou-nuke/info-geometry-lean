import InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
import Mathlib.Data.Fintype.EquivFin

/-!
# Base-fibre bridge from native lines to intrinsic incidence lines

This owner gives the theorem-honest downstream interface for the base fibre.
The named parabolic trio is not a three-distinct representative list, so finite
consumers should route through the whole native `NativeLine` carrier and its
abstract equivalence with the intrinsic base-line fibre.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeIntrinsicLineFiberBridge

open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2ParabolicLineAction
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

theorem nativeLine_card_eq_intrinsicBaseLine_card :
    Fintype.card NativeLine =
      Fintype.card (IntrinsicLine nativeBaseIsotropicPoint) := by
  calc
    Fintype.card NativeLine = 3 := nativeBaseLine_card
    _ = Fintype.card (IntrinsicLine nativeBaseIsotropicPoint) := by
      symm
      exact InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus.intrinsicLine_base_card

noncomputable def nativeLineCardinalityEquivBaseIntrinsicLine :
    NativeLine ≃ IntrinsicLine nativeBaseIsotropicPoint := by
  exact Fintype.equivOfCardEq nativeLine_card_eq_intrinsicBaseLine_card

theorem nativeLineCardinalityEquivBaseIntrinsicLine_surjective :
    Function.Surjective
      (nativeLineCardinalityEquivBaseIntrinsicLine :
        NativeLine → IntrinsicLine nativeBaseIsotropicPoint) :=
  nativeLineCardinalityEquivBaseIntrinsicLine.surjective

theorem not_three_distinct_named_parabolic_lines :
    ¬ (lineZero ≠ lineInfinity ∧ lineInfinity ≠ lineOne ∧ lineZero ≠ lineOne) :=
  InfoGeometry.Algebra.Zorn.G2NativeLineFiberDistinctness.not_three_distinct_named_parabolic_lines

end InfoGeometry.Algebra.Zorn.G2NativeIntrinsicLineFiberBridge
