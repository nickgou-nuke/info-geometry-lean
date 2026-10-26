/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CyclicMatrixCurvature
import InfoGeometry.Canonical.DiscreteFrameCommutator
import InfoGeometry.Canonical.ZornMovingCornerBoundary

/-! Narrow import/build target and axiom inspection for the intake boundary. -/

#print axioms InfoGeometry.Algebra.CyclicMatrixCurvature.cyclicTrace_mul_comm
#print axioms InfoGeometry.Algebra.CyclicMatrixCurvature.scalar_defect_eq_coboundary
#print axioms InfoGeometry.Algebra.CyclicMatrixCurvature.tracePotential_coboundary_is_cocycle
#print axioms InfoGeometry.Canonical.DiscreteFrameCommutator.frame_commutator
#print axioms InfoGeometry.Canonical.DiscreteFrameCommutator.frame_commutator_ne_one
#print axioms InfoGeometry.Canonical.DiscreteFrameCommutator.frame_not_commute
#print axioms InfoGeometry.Canonical.DiscreteFrameCommutator.frame_not_commute_of_neZero_two
#print axioms InfoGeometry.Canonical.DiscreteFrameCommutator.rephased_frame_commutator
#print axioms InfoGeometry.Canonical.ZornMovingCornerBoundary.moving_corner_eq_zero_iff
#print axioms InfoGeometry.Canonical.ZornMovingCornerBoundary.moving_corner_not_neg_riccati

example :
    InfoGeometry.Canonical.DiscreteFrameCommutator.frameX ℚ *
      InfoGeometry.Canonical.DiscreteFrameCommutator.frameZ ℚ *
      InfoGeometry.Canonical.DiscreteFrameCommutator.frameX ℚ *
      InfoGeometry.Canonical.DiscreteFrameCommutator.frameZ ℚ ≠ 1 := by
  exact InfoGeometry.Canonical.DiscreteFrameCommutator.frame_commutator_ne_one ℚ
    (by norm_num)
