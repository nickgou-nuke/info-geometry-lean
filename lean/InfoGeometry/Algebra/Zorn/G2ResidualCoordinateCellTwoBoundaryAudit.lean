/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellTwoBoundary
import InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellTwo

open InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellTwoBoundary
open InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellTwo
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate

#print axioms residualWord_cell_two_collision
#print axioms residualWord_injective_on_cell_two_is_false
#print axioms residualPair_injective_on_cell_two

example : residualPair 2 170 ≠ residualPair 2 185 := by
  obtain ⟨_, hi, hj, hne⟩ := residualWord_cell_two_collision
  intro h
  exact hne (residualPair_injective_on_cell_two 170 185 hi hj h)
