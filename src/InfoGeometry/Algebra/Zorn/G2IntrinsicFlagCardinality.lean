import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2IntrinsicLineFiberTransport
import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus
import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import Mathlib.Data.Fintype.Card

/-!
# Cardinality interface for the intrinsic flag carrier

This owner records the cardinality consequence of the uniform three-line
fiber statement for the intrinsic incidence carrier.  It proves the
fiber statement and the global 189-flag cardinality unconditionally.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicFlagCardinality

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
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

theorem intrinsicFlag_card :
    Fintype.card IntrinsicFlag = 189 :=
  intrinsicFlag_card_of_uniform_fiber
    InfoGeometry.Algebra.Zorn.G2IntrinsicBaseLineCensus.intrinsicLineFiber_card_eq_three

end InfoGeometry.Algebra.Zorn.G2IntrinsicFlagCardinality
