import Mathlib.Data.Matrix.Basic
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

theorem test_simp :
  InfoGeometry.Canonical.ZornMatrix.mul (circularPeirceBasis 0) zornPlus = circularPeirceBasis 0 := by
  simp [-circularPeirceBasis_apply, circularPeirceBasis_mul_zornPlus]
