import InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
import InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
import Mathlib.Data.Fintype.Card

/-! Cardinality interface for the native full-flag carrier. -/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagCardinality

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeFullFlagCarrier
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber

theorem nativeFlag_card_of_uniform_fiber
    (hfiber : ∀ p : OctImIsotropicPoint,
      Fintype.card (NativeLinesThroughPoint p.1) = 3) :
    Fintype.card NativeFlag = 189 := by
  classical
  change Fintype.card (Σ p : OctImIsotropicPoint,
    NativeLinesThroughPoint p.1) = 189
  rw [Fintype.card_sigma]
  calc
    (∑ p : OctImIsotropicPoint,
      Fintype.card (NativeLinesThroughPoint p.1)) =
        ∑ _p : OctImIsotropicPoint, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hfiber]
    _ = Fintype.card OctImIsotropicPoint * 3 := by simp
    _ = 189 := by rw [octImIsotropicPoint_card]

theorem nativeFlag_card : Fintype.card NativeFlag = 189 := by
  exact nativeFlag_card_of_uniform_fiber
    InfoGeometry.Algebra.Zorn.G2NativeLineFiberTransport.nativeLineFiber_card_eq_three

end InfoGeometry.Algebra.Zorn.G2NativeFlagCardinality
