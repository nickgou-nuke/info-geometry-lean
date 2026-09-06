import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
import InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import Mathlib.Data.Fintype.Card

/-!
# Cardinality interface for the intrinsic flag carrier

This owner closes the intrinsic flag cardinality from native incidence geometry:
the base fibre has exactly three intrinsic lines, point transitivity transports
that cardinality to every fibre, and the 63-point base yields 189 flags.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicFlagCardinality

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
open InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus

theorem intrinsicFlag_card_of_uniform_fiber
    (hfiber : ∀ p : OctImIsotropicPoint,
      Fintype.card (IntrinsicLine p) = 3) :
    Fintype.card IntrinsicFlag = 189 := by
  classical
  change Fintype.card (Σ p : OctImIsotropicPoint, IntrinsicLine p) = 189
  rw [Fintype.card_sigma]
  calc
    (∑ p : OctImIsotropicPoint, Fintype.card (IntrinsicLine p)) =
        ∑ _p : OctImIsotropicPoint, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hfiber]
    _ = Fintype.card OctImIsotropicPoint * 3 := by simp
    _ = 189 := by rw [octImIsotropicPoint_card]

/-- Every intrinsic point lies on exactly three intrinsic lines.  This is the
native uniform-fibre theorem obtained by transporting the certified base-line
census along the already-proved transitive point action. -/
theorem intrinsicLine_card_eq_three
    (p : OctImIsotropicPoint) :
    Fintype.card (IntrinsicLine p) = 3 := by
  calc
    Fintype.card (IntrinsicLine p) =
        Fintype.card (IntrinsicLine
          InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer.nativeBaseIsotropicPoint) :=
      intrinsicLineFiber_card_eq_base_of_point_transitive p
    _ = 3 := intrinsicLine_base_card

/-- The intrinsic flag carrier has exactly 189 elements, unconditionally from
native point transitivity and the three-line fibre census. -/
theorem intrinsicFlag_card :
    Fintype.card IntrinsicFlag = 189 := by
  exact intrinsicFlag_card_of_uniform_fiber intrinsicLine_card_eq_three

end InfoGeometry.Algebra.Zorn.G2IntrinsicFlagCardinality
