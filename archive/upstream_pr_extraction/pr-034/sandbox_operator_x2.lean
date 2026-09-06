import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open Finset

theorem circular_left_zornPlus_coord (x : Coord) (i : Fin 8) :
    circularL zornPlus x i = if i.val < 4 then x i else 0 := by
  sorry
