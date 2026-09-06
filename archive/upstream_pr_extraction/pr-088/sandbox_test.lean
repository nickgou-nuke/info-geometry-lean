import Mathlib.Data.Matrix.Basic
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

theorem test_left :
  circularPeirceBasis 0 * zornPlus = circularPeirceBasis 0 :=
by exact circularPeirceBasis_mul_zornPlus 0
