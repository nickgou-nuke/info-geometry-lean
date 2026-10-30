/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.DikinApolloniusTrap

/-!
# Strictness audit for the equilibrium Dikin estimate

The owner theorem proves a weak quadratic bound and allows `Kc = 1`. This
boundary witness shows that those hypotheses do not imply a strict bound.
For `Kc < 1` and positive radius, the same estimate is strict.
-/

namespace InfoGeometry.Quantum.DikinApolloniusTrap

/-- At unit contraction factor, the boundary point remains on the boundary;
the hypotheses of `blahut_arimoto_dikin_shrinkage` do not imply strictness. -/
theorem unit_factor_equilibrium_boundary_counterexample :
    ∃ Kc r y Ty : ℝ,
      0 ≤ Kc ∧ y ∈ dikinEquilibriumEllipsoid r ∧
      |Ty| ≤ Kc * |y| ∧ ¬ 2 * Ty ^ 2 < (Kc * r) ^ 2 := by
  refine ⟨1, Real.sqrt 2, 1, 1, by norm_num, ?_, by norm_num, ?_⟩
  · rw [dikin_equilibrium_ellipsoid_iff]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  · rw [one_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

/-- A strict contraction factor and positive radius place the image strictly
inside the original radius-`r` equilibrium ellipsoid. -/
theorem blahut_arimoto_dikin_strict_shrinkage
    (Kc r y Ty : ℝ) (hKc_nonneg : 0 ≤ Kc) (hKc_lt : Kc < 1)
    (hr : 0 < r) (hy_in : y ∈ dikinEquilibriumEllipsoid r)
    (h_contraction : |Ty| ≤ Kc * |y|) :
    2 * Ty ^ 2 < r ^ 2 := by
  have hweak := blahut_arimoto_dikin_shrinkage Kc r y hKc_nonneg hy_in Ty h_contraction
  have hKc_sq : Kc ^ 2 < 1 := by nlinarith [mul_pos (sub_pos.mpr hKc_lt) (by linarith : 0 < 1 + Kc)]
  have hr_sq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hstrict : (Kc * r) ^ 2 < r ^ 2 := by
    calc
      (Kc * r) ^ 2 = Kc ^ 2 * r ^ 2 := by rw [mul_pow]
      _ < 1 * r ^ 2 := mul_lt_mul_of_pos_right hKc_sq hr_sq
      _ = r ^ 2 := one_mul _
  exact lt_of_le_of_lt hweak hstrict

#print axioms unit_factor_equilibrium_boundary_counterexample
#print axioms blahut_arimoto_dikin_strict_shrinkage

end InfoGeometry.Quantum.DikinApolloniusTrap
