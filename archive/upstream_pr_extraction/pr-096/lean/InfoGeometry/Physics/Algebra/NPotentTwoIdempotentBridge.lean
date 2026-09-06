/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.AffineConformalHullNPotencyBridge

/-!
# The two-potent boundary is the idempotent boundary

This is the smallest native algebraic fragment of the n-potent dictionary.
It records only the polynomial identity; no spectral interpretation is used.
-/

namespace InfoGeometry.Physics.Algebra.NPotentTwoIdempotentBridge

open InfoGeometry.Canonical.AffineConformalHullNPotencyBridge

theorem inHull_two_iff_idempotent (z : ℂ) :
    inHull 2 z ↔ z * z = z := by
  simp [inHull, pow_two]

theorem inHull_two_iff_zero_or_one (z : ℂ) :
    inHull 2 z ↔ z = 0 ∨ z = 1 := by
  rw [inHull_iff_zero_or_rootOfUnity 2 (by norm_num)]
  simp

theorem inHull_three_iff_zero_or_one_or_neg_one (z : ℂ) :
    inHull 3 z ↔ z = 0 ∨ z = 1 ∨ z = -1 := by
  rw [inHull_iff_zero_or_rootOfUnity 3 (by norm_num)]
  rw [sq_eq_one_iff]

end InfoGeometry.Physics.Algebra.NPotentTwoIdempotentBridge
