/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# Algebraic sectors of an n-potent element

For `x ^ n = x`, the element `x ^ (n - 1)` is an idempotent and its
complement is an orthogonal idempotent.  This is purely ring-theoretic and
does not invoke an analytic spectrum.
-/

namespace InfoGeometry.Physics.Algebra.NPotentIdempotentDecomposition

theorem npotent_nonzero_sector_idempotent
    {R : Type*} [CommRing R] {x : R} {n : ℕ}
    (hn : 2 ≤ n) (hx : x ^ n = x) :
    (x ^ (n - 1)) ^ 2 = x ^ (n - 1) := by
  calc
    (x ^ (n - 1)) ^ 2 = x ^ ((n - 1) * 2) := by rw [← pow_mul]
    _ = x ^ (n + (n - 2)) := by congr 1; omega
    _ = x ^ n * x ^ (n - 2) := by rw [pow_add]
    _ = x * x ^ (n - 2) := by rw [hx]
    _ = x ^ (n - 1) := by
      calc
        x * x ^ (n - 2) = x ^ 1 * x ^ (n - 2) := by rw [pow_one]
        _ = x ^ (1 + (n - 2)) := by rw [pow_add]
        _ = x ^ (n - 1) := by congr 1; omega

theorem npotent_zero_sector_idempotent
    {R : Type*} [CommRing R] {x : R} {n : ℕ}
    (hn : 2 ≤ n) (hx : x ^ n = x) :
    (1 - x ^ (n - 1)) ^ 2 = 1 - x ^ (n - 1) := by
  have hP := npotent_nonzero_sector_idempotent hn hx
  calc
    (1 - x ^ (n - 1)) ^ 2 =
        1 - 2 * x ^ (n - 1) + (x ^ (n - 1)) ^ 2 := by ring
    _ = 1 - x ^ (n - 1) := by rw [hP]; ring

theorem npotent_sectors_orthogonal
    {R : Type*} [CommRing R] {x : R} {n : ℕ}
    (hn : 2 ≤ n) (hx : x ^ n = x) :
    (1 - x ^ (n - 1)) * x ^ (n - 1) = 0 ∧
      x ^ (n - 1) * (1 - x ^ (n - 1)) = 0 := by
  have hP := npotent_nonzero_sector_idempotent hn hx
  constructor
  · calc
      (1 - x ^ (n - 1)) * x ^ (n - 1) =
          x ^ (n - 1) - (x ^ (n - 1)) ^ 2 := by ring
      _ = 0 := by rw [hP]; ring
  · calc
      x ^ (n - 1) * (1 - x ^ (n - 1)) =
          x ^ (n - 1) - (x ^ (n - 1)) ^ 2 := by ring
      _ = 0 := by rw [hP]; ring

theorem npotent_sectors_resolve_identity
    {R : Type*} [CommRing R] {x : R} {n : ℕ} :
    (1 - x ^ (n - 1)) + x ^ (n - 1) = 1 := by
  ring

end InfoGeometry.Physics.Algebra.NPotentIdempotentDecomposition
