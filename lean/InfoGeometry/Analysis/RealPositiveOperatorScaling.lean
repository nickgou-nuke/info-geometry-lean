/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.Linarith

/-!
# Positive rescaling and the absence of a common coercivity bound

Nonzero quadratic rescaling preserves the full kernel of a native real
endomorphism and its orthogonal complement. Its quadratic form scales by
the same factor. If that complement contains a nonzero vector, no positive
coercivity constant works for all positive rescalings.

The nonzero-vector hypothesis is explicit. The result does not contradict
the positive bound for each fixed finite-dimensional positive operator.
-/

noncomputable section

namespace InfoGeometry.Analysis.RealPositiveOperatorScaling

open scoped InnerProductSpace

section AlgebraicKernel

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Nonzero quadratic rescaling preserves every zero mode of the endomorphism. -/
theorem ker_quadratic_smul (T : Module.End ℝ E) {r : ℝ} (hr : r ≠ 0) :
    ((r * r) • T).ker = T.ker :=
  LinearMap.ker_smul T (r * r) (mul_ne_zero hr hr)

end AlgebraicKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal complement of the entire kernel is preserved as well. -/
theorem ker_orthogonal_quadratic_smul (T : Module.End ℝ E) {r : ℝ} (hr : r ≠ 0) :
    ((r * r) • T).kerᗮ = T.kerᗮ := by
  rw [ker_quadratic_smul T hr]

/-- Every real quadratic rescaling preserves native operator positivity. -/
theorem isPositive_quadratic_smul (T : Module.End ℝ E) (hT : T.IsPositive) (r : ℝ) :
    ((r * r) • T).IsPositive :=
  hT.smul_of_nonneg (mul_self_nonneg r)

/-- This is the quadratic form of the actual scaled endomorphism. -/
theorem inner_quadratic_smul (T : Module.End ℝ E) (r : ℝ) (x : E) :
    inner ℝ x (((r * r) • T) x) = (r * r) * inner ℝ x (T x) := by
  rw [LinearMap.smul_apply, real_inner_smul_right]

/-- Positive scaling makes the operator's energy on a fixed nonzero vector
smaller than any prescribed positive quadratic bound. -/
theorem exists_positive_scaling_inner_lt (T : Module.End ℝ E) (hT : T.IsPositive)
    (x : E) (hx : x ≠ 0) (c : ℝ) (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧
      inner ℝ x (((r * r) • T) x) < c * ‖x‖ ^ 2 := by
  let e := inner ℝ x (T x)
  let q := c * ‖x‖ ^ 2
  have he : 0 ≤ e := hT.inner_nonneg_right x
  have hq : 0 < q := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hx))
  have hden : 0 < e + 1 := by linarith
  let r := min 1 (q / (e + 1))
  have hr : 0 < r := lt_min zero_lt_one (div_pos hq hden)
  have hrone : r ≤ 1 := min_le_left _ _
  have hrq : r * (e + 1) ≤ q :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hrsq : r * r ≤ r := by
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hrone)]
  have hre : r * e < q := by nlinarith
  refine ⟨r, hr, ?_⟩
  rw [inner_quadratic_smul]
  exact (mul_le_mul_of_nonneg_right hrsq he).trans_lt hre

/-- A nonzero vector in the actual kernel complement rules out a common
positive coercivity constant across all positive rescalings. -/
theorem not_exists_uniform_positive_coercive_bound
    (T : Module.End ℝ E) (hT : T.IsPositive)
    (hactive : ∃ x : E, x ∈ T.kerᗮ ∧ x ≠ 0) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ x ∈ ((r * r) • T).kerᗮ,
        c * ‖x‖ ^ 2 ≤ inner ℝ x (((r * r) • T) x) := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨x, hx, hx0⟩ := hactive
  obtain ⟨r, hr, hsmall⟩ := exists_positive_scaling_inner_lt T hT x hx0 c hc
  have hxscaled : x ∈ ((r * r) • T).kerᗮ := by
    rw [ker_orthogonal_quadratic_smul T hr.ne']
    exact hx
  exact hsmall.not_ge (hbound r hr x hxscaled)

end InfoGeometry.Analysis.RealPositiveOperatorScaling
