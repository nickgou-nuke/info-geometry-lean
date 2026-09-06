import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout

open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore

theorem right_uMinus_test (i : Fin 8) :
  circularPeirceBasis i * zornMinus =
    if i.val = 0 then 0
    else if i.val < 5 then circularPeirceBasis i
    else 0 := by
  fin_cases i <;>
    simp [circularPeirceBasis, zornMinus, chiralUpperBasis, chiralLowerBasis] <;> rfl
