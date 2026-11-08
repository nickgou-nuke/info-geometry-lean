/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.RingQuot
import InfoGeometry.Core.DualSeedPeirce
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Topology.CuntzCantorSpectralTriple

namespace InfoGeometry.Canonical.CuntzDualSeedPairBridge

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Topology

variable {Op : Type*} [Ring Op] [StarRing Op]

section CuntzRangeProjections

variable (C : CuntzO2Carrier Op)

theorem leftRangeProjection_idempotent :
    C.leftRangeProjection * C.leftRangeProjection = C.leftRangeProjection := by
  exact C.leftRangeProjection_subequiv_self

end CuntzRangeProjections

section CuntzToDualSeedPair

variable (C : CuntzO2Carrier Op)

def cuntz_d (C : CuntzO2Carrier Op) : Op := C.S_left * star C.S_right
def cuntz_B (C : CuntzO2Carrier Op) : Op := C.S_right * star C.S_left

theorem cuntz_d_sq_zero (C : CuntzO2Carrier Op) : cuntz_d C * cuntz_d C = 0 := by
  calc (C.S_left * star C.S_right) * (C.S_left * star C.S_right)
      = C.S_left * (star C.S_right * C.S_left) * star C.S_right := by noncomm_ring
    _ = C.S_left * 0 * star C.S_right := by rw [C.orthogonal_ranges.2]
    _ = 0 := by simp

theorem cuntz_B_sq_zero (C : CuntzO2Carrier Op) : cuntz_B C * cuntz_B C = 0 := by
  calc (C.S_right * star C.S_left) * (C.S_right * star C.S_left)
      = C.S_right * (star C.S_left * C.S_right) * star C.S_left := by noncomm_ring
    _ = C.S_right * 0 * star C.S_left := by rw [C.orthogonal_ranges.1]
    _ = 0 := by simp

theorem cuntz_induces_dual_seed_pair (C : CuntzO2Carrier Op) : IsDualSeedPair (cuntz_d C) (cuntz_B C) := by
  refine ⟨cuntz_d_sq_zero C, cuntz_B_sq_zero C, ?_, ?_⟩
  · calc (C.S_left * star C.S_right) * (C.S_right * star C.S_left) * (C.S_left * star C.S_right)
        = C.S_left * (star C.S_right * C.S_right) * (star C.S_left * C.S_left) * star C.S_right := by noncomm_ring
      _ = C.S_left * 1 * 1 * star C.S_right := by rw [C.right_isometry, C.left_isometry] <;> simp [mul_assoc]
      _ = C.S_left * star C.S_right := by simp [mul_assoc]
  · calc (C.S_right * star C.S_left) * (C.S_left * star C.S_right) * (C.S_right * star C.S_left)
        = C.S_right * (star C.S_left * C.S_left) * (star C.S_right * C.S_right) * star C.S_left := by noncomm_ring
      _ = C.S_right * 1 * 1 * star C.S_left := by rw [C.left_isometry, C.right_isometry] <;> simp [mul_assoc]
      _ = C.S_right * star C.S_left := by simp [mul_assoc]

end CuntzToDualSeedPair

end InfoGeometry.Canonical.CuntzDualSeedPairBridge