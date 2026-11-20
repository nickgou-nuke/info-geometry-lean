/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness
import InfoGeometry.OperatorAlgebra.RealSkewDomainResidual
import Mathlib.Tactic.Abel

/-!
# Residual bounds for the existing maximal real ℓ² operator

This consumer uses `K_max` on its actual domain `D_max`. Its proved domain
skew symmetry instantiates the generic residual estimate. The operator is not
replaced by a finite or bounded model. Arithmetic modes are not constructed.
-/

namespace InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness

open RealSkewDomainResidual

/-- Pythagoras for a real shift of the existing unbounded operator. -/
theorem K_max_shift_norm_sq (v : D_max) (a : ℝ) :
    ‖K_max v - a • (v : H_lp)‖ ^ 2 = ‖K_max v‖ ^ 2 + a ^ 2 * ‖(v : H_lp)‖ ^ 2 := by
  simpa using residual_norm_sq K_max K_max_skew_symmetric
    (0 : H_lp →ₗ[ℝ] H_lp) v a 0 (by simp)

/-- Quantitative lower bound for the actual maximal-domain residual. -/
theorem K_max_shift_norm_lower_bound (v : D_max) (a : ℝ) :
    |a| * ‖(v : H_lp)‖ ≤ ‖K_max v - a • (v : H_lp)‖ := by
  simpa using abs_parameter_mul_norm_le_residual K_max K_max_skew_symmetric
    (0 : H_lp →ₗ[ℝ] H_lp) v a 0 (by simp)

/-- A normalized approximate real eigenvector has residual at least `|a|`. -/
theorem K_max_normalized_shift_lower_bound (v : D_max) (a : ℝ)
    (hv : ‖(v : H_lp)‖ = 1) : |a| ≤ ‖K_max v - a • (v : H_lp)‖ := by
  simpa [hv] using K_max_shift_norm_lower_bound v a

/-- Nonzero real shifts are injective on the existing maximal domain. -/
theorem K_max_shift_injective (a : ℝ) (ha : a ≠ 0) :
    Function.Injective (fun v : D_max => K_max v - a • (v : H_lp)) := by
  intro u v huv
  have hres : K_max (u - v) - a • ((u - v : D_max) : H_lp) = 0 := by
    simp only [map_sub, Submodule.coe_sub, smul_sub]
    calc
      K_max u - K_max v - (a • (u : H_lp) - a • (v : H_lp)) =
          (K_max u - a • (u : H_lp)) - (K_max v - a • (v : H_lp)) := by abel
      _ = 0 := sub_eq_zero.mpr huv
  have hb := K_max_shift_norm_lower_bound (u - v) a
  rw [hres, norm_zero] at hb
  have hz : ‖((u - v : D_max) : H_lp)‖ = 0 := by
    have hp : 0 < |a| := abs_pos.mpr ha
    nlinarith [norm_nonneg ((u - v : D_max) : H_lp)]
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact norm_eq_zero.mp hz

end InfoGeometry.OperatorAlgebra.UnboundedHilbertResolventAndC0GroupWitness
