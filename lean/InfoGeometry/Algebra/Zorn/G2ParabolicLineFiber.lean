import InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Card

/-! Shared finite Peirce line carrier. -/
namespace InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber

export InfoGeometry.Algebra.Zorn.G2ParabolicLineCarrier
  (OctImF2 splitQuad octCross canonicalBasePoint)

/-! Legacy `octCross` carrier.  It is intentionally kept separate from the
native split-Zorn carrier until an incidence equivalence is proved. -/
def basePoint : OctImF2 := fun k => if k = 0 then 1 else 0

def isG2FlagTransversal (x₀ y : OctImF2) : Bool :=
  (y ≠ 0) && (y 0 == 0) && (splitQuad x₀ == 0) &&
  (splitQuad y == 0) && (octCross x₀ y == 0)

def LinesThroughPoint (x₀ : OctImF2) : Type :=
  { y : OctImF2 // isG2FlagTransversal x₀ y = true }

instance (x₀ : OctImF2) : Fintype (LinesThroughPoint x₀) := by
  dsimp [LinesThroughPoint]
  infer_instance

instance (x₀ : OctImF2) : DecidableEq (LinesThroughPoint x₀) := by
  dsimp [LinesThroughPoint]
  infer_instance

theorem base_point_lines_card : Fintype.card (LinesThroughPoint basePoint) = 3 := by
  decide

end InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
