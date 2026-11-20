/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.InformationGeometry.BurgSteinSelfConcordance
import InfoGeometry.Parahyperkahler.AnalyticExcision
import Mathlib.Order.Bounds.Image

/-!
# Positive-ray Dikin bounds with the Weyl scale retained

This file consumes the existing logarithmic Fisher metric `(v / x)^2` and
the existing Dikin ellipsoid predicate. A uniform normalized bound controls
the original quantity only after multiplication by its positive base scale.
An explicit adaptive normalization exists for every real sequence, including
unbounded ones. This fact is not an arithmetic cancellation estimate.
-/

noncomputable section

namespace InfoGeometry.Analysis.DikinWeylBoundedness

open InfoGeometry.InformationGeometry.BurgStein
open InfoGeometry.Parahyperkahler.AnalyticExcision

/-- The existing quadratic metric and shifted Dikin predicate describe the same ellipsoid. -/
theorem inDikin_add_iff_fisherScaleMetric {x v R : ℝ} (hx : 0 < x) :
    InDikin x (x + v) R ↔ fisherScaleMetric x v ≤ R ^ 2 := by
  simp only [InDikin, add_sub_cancel_left, fisherScaleMetric, div_pow]
  exact (div_le_iff₀ (sq_pos_of_pos hx)).symm

/-- Restoring a positive scale converts the quadratic bound into an absolute bound. -/
theorem fisherScaleMetric_le_sq_iff {x v R : ℝ} (hx : 0 < x) (hR : 0 ≤ R) :
    fisherScaleMetric x v ≤ R ^ 2 ↔ |v| ≤ R * x := by
  rw [fisherScaleMetric, sq_le_sq, abs_div, abs_of_pos hx, abs_of_nonneg hR,
    div_le_iff₀ hx]

/-- Strict normalized bounds retain exactly the same scale factor. -/
theorem fisherScaleMetric_lt_sq_iff {x v R : ℝ} (hx : 0 < x) (hR : 0 < R) :
    fisherScaleMetric x v < R ^ 2 ↔ |v| < R * x := by
  rw [fisherScaleMetric, sq_lt_sq, abs_div, abs_of_pos hx, abs_of_pos hR,
    div_lt_iff₀ hx]

/-- Common nonzero Weyl scaling preserves the actual logarithmic Fisher quadratic. -/
theorem fisherScaleMetric_common_mul (x v : ℝ) {c : ℝ} (hc : c ≠ 0) :
    fisherScaleMetric (c * x) (c * v) = fisherScaleMetric x v := by
  unfold fisherScaleMetric
  rw [mul_div_mul_left v x hc]

/-- Bounded normalized quadratics are precisely uniform absolute bounds with scale restored. -/
theorem bddAbove_fisherScaleMetric_range_iff {ι : Type*} (x v : ι → ℝ)
    (hx : ∀ i, 0 < x i) :
    BddAbove (Set.range fun i => fisherScaleMetric (x i) (v i)) ↔
      ∃ R : ℝ, 0 ≤ R ∧ ∀ i, |v i| ≤ R * x i := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨Real.sqrt (max B 0), Real.sqrt_nonneg _, fun i => ?_⟩
    apply (fisherScaleMetric_le_sq_iff (hx i) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (le_max_right B 0)]
    exact (hB (Set.mem_range_self i)).trans (le_max_left B 0)
  · rintro ⟨R, hR, hv⟩
    refine ⟨R ^ 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (fisherScaleMetric_le_sq_iff (hx i) hR).mpr (hv i)

/-- A bound on the base scale is required to transfer a normalized estimate to a chosen weight. -/
theorem abs_le_of_fisherScaleMetric_and_scale_bound {x v R C w : ℝ}
    (hx : 0 < x) (hR : 0 ≤ R)
    (hv : fisherScaleMetric x v ≤ R ^ 2) (hxw : x ≤ C * w) :
    |v| ≤ (R * C) * w := by
  calc
    |v| ≤ R * x := (fisherScaleMetric_le_sq_iff hx hR).mp hv
    _ ≤ R * (C * w) := mul_le_mul_of_nonneg_left hxw hR
    _ = (R * C) * w := (mul_assoc _ _ _).symm

/-- Every real value has a constructive positive normalization of radius strictly below one half. -/
theorem fisherScaleMetric_adaptive_lt_quarter (v : ℝ) :
    fisherScaleMetric (1 + 2 * |v|) v < (1 / 2 : ℝ) ^ 2 := by
  apply (fisherScaleMetric_lt_sq_iff (by positivity) (by norm_num)).mpr
  nlinarith [abs_nonneg v]

/-- Adaptive normalization makes every real sequence bounded in its varying Dikin metric. -/
theorem bddAbove_adaptive_fisherScaleMetric {ι : Type*} (v : ι → ℝ) :
    BddAbove (Set.range fun i => fisherScaleMetric (1 + 2 * |v i|) (v i)) := by
  refine ⟨(1 / 2 : ℝ) ^ 2, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (fisherScaleMetric_adaptive_lt_quarter (v i)).le

/-- A concrete unbounded sequence still has uniformly bounded adaptive Dikin quadratics. -/
theorem adaptive_dikin_bound_without_bddAbove :
    ∃ v : ℕ → ℝ,
      BddAbove (Set.range fun i => fisherScaleMetric (1 + 2 * |v i|) (v i)) ∧
      ¬ BddAbove (Set.range v) := by
  refine ⟨fun N => (N : ℝ), bddAbove_adaptive_fisherScaleMetric _, ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨N, hN⟩ := exists_nat_gt B
  exact (not_le_of_gt hN) (hB (Set.mem_range_self N))

end InfoGeometry.Analysis.DikinWeylBoundedness
