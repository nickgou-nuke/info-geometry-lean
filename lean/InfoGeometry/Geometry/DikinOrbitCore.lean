/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Canonical inverse-square Dikin geometry on the real orbit coordinate

This owner defines the shared coefficient and ellipsoid predicate used by the
Blahut-orbit and Cartan–Dickson lanes. The analytic domain restriction `x > 0`
is stated on theorems that need it; the raw coefficient remains defined on all
of `ℝ`, matching the existing public definitions.
-/

namespace InfoGeometry.Geometry.DikinOrbitCore

noncomputable section

/-- The inverse-square Dikin coefficient `1 / x²` on the real coordinate. -/
def coefficient (x : ℝ) : ℝ := 1 / x ^ 2

/-- The corresponding one-dimensional quadratic form on a tangent `v`. -/
def quadratic (x v : ℝ) : ℝ := coefficient x * v ^ 2

/-- The radius-`r` sublevel predicate centered at `x`. -/
def ellipsoid (x y r : ℝ) : Prop := quadratic x (y - x) ≤ r ^ 2

theorem coefficient_pos {x : ℝ} (hx : x ≠ 0) : 0 < coefficient x := by
  dsimp [coefficient]
  exact one_div_pos.mpr (sq_pos_of_ne_zero hx)

theorem quadratic_nonneg (x v : ℝ) : 0 ≤ quadratic x v := by
  by_cases hx : x = 0
  · simp [quadratic, coefficient, hx]
  · exact mul_nonneg (le_of_lt (coefficient_pos hx)) (sq_nonneg v)

theorem ellipsoid_iff_abs_le {x y r : ℝ} (hx : 0 < x) (hr : 0 ≤ r) :
    ellipsoid x y r ↔ |y - x| ≤ r * x := by
  unfold ellipsoid quadratic coefficient
  have h_div : (1 / x ^ 2) * (y - x) ^ 2 = ((y - x) / x) ^ 2 := by
    rw [div_pow, one_div_mul_eq_div]
  rw [h_div, sq_le_sq, abs_of_nonneg hr, abs_div, abs_of_pos hx,
    div_le_iff₀ hx]

end

end InfoGeometry.Geometry.DikinOrbitCore
