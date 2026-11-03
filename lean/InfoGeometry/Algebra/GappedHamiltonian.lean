/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Basic

/-!
# Commutation of operator powers

In an associative ring, an operator commuting with `X` commutes with every
natural power of that operator. This algebraic fact does not assert spectral
gap stability or invertibility; those require additional analytic structure.
-/

namespace InfoGeometry.Algebra.GappedHamiltonian

variable {R : Type*} [Monoid R]

/-- If `H` commutes with `X`, then each natural power of `H` commutes with `X`. -/
theorem commutes_with_powers {H X : R} (h_comm : H * X = X * H) :
    ∀ n : ℕ, H ^ n * X = X * H ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        H ^ (n + 1) * X = (H ^ n * H) * X := by rw [pow_succ]
        _ = H ^ n * (H * X) := by rw [mul_assoc]
        _ = H ^ n * (X * H) := by rw [h_comm]
        _ = (H ^ n * X) * H := by rw [mul_assoc]
        _ = (X * H ^ n) * H := by rw [ih]
        _ = X * (H ^ n * H) := by rw [mul_assoc]
        _ = X * H ^ (n + 1) := by rw [pow_succ]

end InfoGeometry.Algebra.GappedHamiltonian
