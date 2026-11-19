/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Centered norm bounds for real symmetric operators

The midpoint and half-width of a real interval convert its native Loewner
operator bounds into an equivalent bound for the actual operator norm.
The proof uses Mathlib's Rayleigh-quotient norm theorem for symmetric bounded
operators; it is not an entrywise matrix norm or a scalar polynomial identity.

Convex interpolation with the identity preserves the interval enlarged to
include `1`. The original interval is preserved when it already contains `1`.
-/

noncomputable section

namespace InfoGeometry.Analysis.RealOperatorGapCentering

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The operator norm of a real symmetric operator is detected by its
quadratic form. -/
theorem norm_le_iff_quadratic_abs (T : E →L[ℝ] E) (hT : T.IsSymmetric)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖T‖ ≤ r ↔ ∀ x, |inner ℝ x (T x)| ≤ r * ‖x‖ ^ 2 := by
  constructor
  · intro h x
    have hx := (T.rayleighQuotient_le_norm x).trans h
    by_cases hx0 : x = 0
    · simp [hx0]
    have hn : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      real_inner_comm, abs_div, abs_of_nonneg (sq_nonneg ‖x‖), div_le_iff₀ hn] using hx
  · intro h
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro x
    by_cases hx0 : x = 0
    · simpa [hx0] using hr
    have hn : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      real_inner_comm, abs_div, abs_of_nonneg (sq_nonneg ‖x‖), div_le_iff₀ hn] using h x

/-- A lower Loewner bound for a symmetric operator is exactly a lower bound
for all of its quadratic evaluations. -/
theorem scalar_le_iff_quadratic (Q : E →L[ℝ] E) (hQ : Q.IsSymmetric) (a : ℝ) :
    a • (1 : E →L[ℝ] E) ≤ Q ↔
      ∀ x, a * ‖x‖ ^ 2 ≤ inner ℝ x (Q x) := by
  rw [ContinuousLinearMap.le_def]
  constructor
  · intro h x
    have hx := h.inner_nonneg_right x
    simpa only [sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, sub_nonneg] using hx
  · intro h
    refine ⟨hQ.sub (LinearMap.IsSymmetric.one.smul (by simp)), fun x => ?_⟩
    have hx := sub_nonneg.mpr (h x)
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      real_inner_comm, sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq] using hx

/-- The analogous quadratic characterization of an upper Loewner bound. -/
theorem le_scalar_iff_quadratic (Q : E →L[ℝ] E) (hQ : Q.IsSymmetric) (b : ℝ) :
    Q ≤ b • (1 : E →L[ℝ] E) ↔
      ∀ x, inner ℝ x (Q x) ≤ b * ‖x‖ ^ 2 := by
  rw [ContinuousLinearMap.le_def]
  constructor
  · intro h x
    have hx := h.inner_nonneg_right x
    simpa only [sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, sub_nonneg] using hx
  · intro h
    refine ⟨(LinearMap.IsSymmetric.one.smul (by simp)).sub hQ, fun x => ?_⟩
    have hx := sub_nonneg.mpr (h x)
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      real_inner_comm, sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq] using hx

/-- Centering a real symmetric operator at the interval midpoint turns its
quadratic interval into an exact operator-norm bound. -/
theorem centered_norm_iff_quadratic_interval (Q : E →L[ℝ] E)
    (hQ : Q.IsSymmetric) {a b : ℝ} (hab : a ≤ b) :
    ‖Q - ((a + b) / 2) • (1 : E →L[ℝ] E)‖ ≤ (b - a) / 2 ↔
      ∀ x, a * ‖x‖ ^ 2 ≤ inner ℝ x (Q x) ∧
        inner ℝ x (Q x) ≤ b * ‖x‖ ^ 2 := by
  rw [norm_le_iff_quadratic_abs _
    (hQ.sub (LinearMap.IsSymmetric.one.smul (by simp))) (by linarith [hab])]
  simp only [sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, abs_le]
  constructor <;> intro h x <;> obtain ⟨hl, hu⟩ := h x <;> constructor <;> nlinarith

/-- A genuine real operator norm is equivalent to the native Loewner interval. -/
theorem centered_norm_iff_order_interval (Q : E →L[ℝ] E)
    (hQ : Q.IsSymmetric) {a b : ℝ} (hab : a ≤ b) :
    ‖Q - ((a + b) / 2) • (1 : E →L[ℝ] E)‖ ≤ (b - a) / 2 ↔
      a • (1 : E →L[ℝ] E) ≤ Q ∧ Q ≤ b • (1 : E →L[ℝ] E) := by
  rw [centered_norm_iff_quadratic_interval Q hQ hab,
    scalar_le_iff_quadratic Q hQ a, le_scalar_iff_quadratic Q hQ b]
  exact forall_and

/-- Mixing an interval-bounded operator with the identity stays in the
smallest scalar interval containing the old interval and `1`. -/
theorem identity_mixture_bounds (Q : E →L[ℝ] E) (hQ : Q.IsSymmetric)
    {a b u : ℝ} (hlo : a • (1 : E →L[ℝ] E) ≤ Q)
    (hhi : Q ≤ b • (1 : E →L[ℝ] E)) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) :
    min a 1 • (1 : E →L[ℝ] E) ≤ u • Q + (1 - u) • (1 : E →L[ℝ] E) ∧
      u • Q + (1 - u) • (1 : E →L[ℝ] E) ≤ max b 1 • (1 : E →L[ℝ] E) := by
  have hS : (u • Q + (1 - u) • (1 : E →L[ℝ] E)).IsSymmetric :=
    (hQ.smul (by simp)).add (LinearMap.IsSymmetric.one.smul (by simp))
  rw [scalar_le_iff_quadratic _ hS, le_scalar_iff_quadratic _ hS]
  have hlo' := (scalar_le_iff_quadratic Q hQ a).mp hlo
  have hhi' := (le_scalar_iff_quadratic Q hQ b).mp hhi
  constructor
  · intro x
    have hqx := mul_le_mul_of_nonneg_left (hlo' x) hu₀
    have ham := mul_le_mul_of_nonneg_right (min_le_left a 1) (sq_nonneg ‖x‖)
    have h1m := mul_le_mul_of_nonneg_right (min_le_right a 1) (sq_nonneg ‖x‖)
    have ham' := mul_le_mul_of_nonneg_left ham hu₀
    have h1m' := mul_le_mul_of_nonneg_left h1m (sub_nonneg.mpr hu₁)
    simp only [add_apply, smul_apply,
      one_apply_eq_self, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    nlinarith
  · intro x
    have hqx := mul_le_mul_of_nonneg_left (hhi' x) hu₀
    have hbm := mul_le_mul_of_nonneg_right (le_max_left b 1) (sq_nonneg ‖x‖)
    have h1m := mul_le_mul_of_nonneg_right (le_max_right b 1) (sq_nonneg ‖x‖)
    have hbm' := mul_le_mul_of_nonneg_left hbm hu₀
    have h1m' := mul_le_mul_of_nonneg_left h1m (sub_nonneg.mpr hu₁)
    simp only [add_apply, smul_apply,
      one_apply_eq_self, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    nlinarith

/-- An interval containing the identity is preserved without enlargement. -/
theorem identity_mixture_preserves_interval (Q : E →L[ℝ] E) (hQ : Q.IsSymmetric)
    {a b u : ℝ} (hlo : a • (1 : E →L[ℝ] E) ≤ Q)
    (hhi : Q ≤ b • (1 : E →L[ℝ] E)) (ha : a ≤ 1) (hb : 1 ≤ b)
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) :
    a • (1 : E →L[ℝ] E) ≤ u • Q + (1 - u) • (1 : E →L[ℝ] E) ∧
      u • Q + (1 - u) • (1 : E →L[ℝ] E) ≤ b • (1 : E →L[ℝ] E) := by
  simpa only [min_eq_left ha, max_eq_left hb] using
    identity_mixture_bounds Q hQ hlo hhi hu₀ hu₁

end InfoGeometry.Analysis.RealOperatorGapCentering
