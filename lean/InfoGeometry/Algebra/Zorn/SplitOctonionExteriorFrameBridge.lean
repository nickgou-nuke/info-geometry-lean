import InfoGeometry.Algebra.Zorn.SplitOctonionGlobalWittNorm
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The finite `1 + 3 + 3 + 1` exterior-frame readout

This is a graded real coordinate model for the scalar/vector/bivector/
pseudoscalar decomposition.  It is deliberately not an algebra
isomorphism with the split-octonion multiplication.
-/

namespace InfoGeometry.Algebra.Zorn.SplitOctonionExteriorFrameBridge

open InfoGeometry.Algebra.Zorn.SplitOctonionGlobalWittNorm
open ProjectiveAffineConformalClosure55

structure ExteriorFrame3 where
  scalar : ℝ
  vector : Fin 3 → ℝ
  bivector : Fin 3 → ℝ
  pseudoscalar : ℝ

abbrev CoordinateCarrier := (Fin 4 → ℝ) × (Fin 4 → ℝ)

def fromPAC (X : PACSplit44) : CoordinateCarrier :=
  (![X.x0, X.x1, X.x2, X.x3], ![X.y0, X.y1, X.y2, X.y3])

def toPAC (F : ExteriorFrame3) : PACSplit44 where
  x0 := F.scalar
  x1 := F.vector 0
  x2 := F.vector 1
  x3 := F.vector 2
  y0 := F.pseudoscalar
  y1 := F.bivector 0
  y2 := F.bivector 1
  y3 := F.bivector 2

def coordinateToPAC (c : CoordinateCarrier) : PACSplit44 where
  x0 := c.1 0
  x1 := c.1 1
  x2 := c.1 2
  x3 := c.1 3
  y0 := c.2 0
  y1 := c.2 1
  y2 := c.2 2
  y3 := c.2 3

theorem coordinateToPAC_fromPAC (X : PACSplit44) :
    coordinateToPAC (fromPAC X) = X := by
  cases X
  rfl

theorem fromPAC_coordinateToPAC (c : CoordinateCarrier) :
    fromPAC (coordinateToPAC c) = c := by
  rcases c with ⟨x, y⟩
  simp only [fromPAC, coordinateToPAC]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def coordinateCarrierEquiv : CoordinateCarrier ≃ PACSplit44 where
  toFun := coordinateToPAC
  invFun := fromPAC
  left_inv := fromPAC_coordinateToPAC
  right_inv := coordinateToPAC_fromPAC

theorem toPAC_Q44 (F : ExteriorFrame3) :
    Q44 (toPAC F) =
      F.scalar ^ 2 + F.vector 0 ^ 2 + F.vector 1 ^ 2 + F.vector 2 ^ 2 -
        (F.pseudoscalar ^ 2 + F.bivector 0 ^ 2 + F.bivector 1 ^ 2 +
          F.bivector 2 ^ 2) := by
  simp [toPAC, Q44]

theorem toPAC_Q44_eq_grade_difference (F : ExteriorFrame3) :
    Q44 (toPAC F) =
      (F.scalar ^ 2 + F.vector 0 ^ 2 + F.vector 1 ^ 2 + F.vector 2 ^ 2) -
        (F.pseudoscalar ^ 2 + F.bivector 0 ^ 2 + F.bivector 1 ^ 2 +
          F.bivector 2 ^ 2) := by
  exact toPAC_Q44 F

end InfoGeometry.Algebra.Zorn.SplitOctonionExteriorFrameBridge
