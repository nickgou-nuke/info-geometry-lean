/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic

/-! Exact right-power extinction from a recovery factor and a next-step zero. -/
namespace InfoGeometry.Core.RightPowerExtinction

section Ring
variable {R : Type*} [Ring R]

/-- Recovery at step `m` and extinction at step `m+1` determine the exact
right extinction time of every nonzero supported state. -/
theorem right_extinction_iff (a : R) {s b x : R} {m : ℕ}
    (hkill : s * a ^ (m + 1) = 0) (hrec : (s * a ^ m) * b = s)
    (hx : x * s ≠ 0) (r : ℕ) : x * s * a ^ r = 0 ↔ m < r := by
  constructor
  · intro hr
    by_contra hnot
    have hrm : r ≤ m := Nat.le_of_not_gt hnot
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hrm
    have hm : x * s * a ^ m = 0 := by
      rw [ht, pow_add, ← mul_assoc, hr, zero_mul]
    apply hx
    calc
      x * s = (x * s * a ^ m) * b := by
        rw [mul_assoc x s (a ^ m), mul_assoc x (s * a ^ m) b, hrec]
      _ = 0 := by rw [hm, zero_mul]
  · intro hr
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hr)
    rw [ht, pow_add, ← mul_assoc, mul_assoc x s (a ^ (m + 1)),
      hkill, mul_zero, zero_mul]

end Ring

end InfoGeometry.Core.RightPowerExtinction
