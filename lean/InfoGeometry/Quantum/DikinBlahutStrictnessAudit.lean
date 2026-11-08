/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.DikinBlahutOrbits

/-!
# Strictness boundary for finite Dikin ellipsoid contraction

The owner proves a non-strict nested inclusion and permits `Kc = 1`. This
module records the boundary example and proves strict inclusion when the
contraction factor is genuinely below one and the radius is positive.
-/

namespace InfoGeometry.Quantum.DikinBlahutOrbits

/-- At unit factor, a boundary point remains on the original ellipsoid
boundary, so the non-strict owner hypothesis cannot imply strict inclusion. -/
theorem unit_factor_boundary_counterexample :
    InDikinEllipsoid 1 2 (1 : ℝ) ∧
      ¬ (dikinMetric 1 * (2 - 1) ^ 2 < (1 : ℝ) ^ 2) := by
  norm_num [InDikinEllipsoid, dikinMetric]

/-- A genuine contraction maps the smaller-radius ellipsoid strictly inside
the original one, provided the original radius is positive. -/
theorem dikin_ellipsoid_nested_strict_shrink
    (x y r Kc : ℝ) (hx : 0 < x) (hr : 0 < r)
    (hKc_nonneg : 0 ≤ Kc) (hKc_lt : Kc < 1)
    (h_in : InDikinEllipsoid x y (Kc * r)) :
    dikinMetric x * (y - x) ^ 2 < r ^ 2 := by
  have hKc_sq : Kc ^ 2 < 1 := by
    have hprod : 0 < (1 - Kc) * (1 + Kc) :=
      mul_pos (sub_pos.mpr hKc_lt) (by linarith)
    nlinarith
  have hr_sq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hrad : (Kc * r) ^ 2 < r ^ 2 := by
    calc
      (Kc * r) ^ 2 = Kc ^ 2 * r ^ 2 := by rw [mul_pow]
      _ < 1 * r ^ 2 := mul_lt_mul_of_pos_right hKc_sq hr_sq
      _ = r ^ 2 := one_mul _
  exact lt_of_le_of_lt h_in hrad

#print axioms unit_factor_boundary_counterexample
#print axioms dikin_ellipsoid_nested_strict_shrink

end InfoGeometry.Quantum.DikinBlahutOrbits
