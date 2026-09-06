import Mathlib.Data.Matrix.Basic
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

theorem test_left_simp :
  InfoGeometry.Canonical.ZornMatrix.mul zornPlus (circularPeirceBasis 0) = circularPeirceBasis 0 := by
  simp [-circularPeirceBasis_apply, zornPlus_mul_circularPeirceBasis]
