import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout

open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

theorem circular_left_zornPlus (x : Coord) :
    circularL (cartesianZornLinearEquiv scalarPlus) x = fun i => if i.val < 4 then x i else 0 := by
  sorry
