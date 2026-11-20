/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.ScaledEulerNN

/-!
# Constructive cutoff scaling and its uniformity obstruction

The existing one-mode criterion gives the exact positive multiplier
`(1 + q₀)^2 / (4 * q₀)` on a fixed nonempty cutoff interval `[q₀, 1)`.
The explicit choice `q = 1 / (8 * (|B| + 1))` makes the required multiplier
larger than any proposed real bound `B`. Consequently no fixed positive
multiplier satisfies the Euler-mode NN slot inequality for every `0 < q < 1`.

These are inequalities for the existing explicit derivative slots. The cutoff
multiplier is constant on its chosen interval. A point-dependent rescaling of
slots is not asserted to be the derivative data of a rescaled potential.
-/

namespace InfoGeometry.Arithmetic.SelfConcordantZetaBarrierProofs

/-- The exact cutoff threshold is a constructive multiplier on the entire
nonempty interval `[q₀, 1)`. -/
theorem scaledEuler_NN_at_cutoff_threshold (E q₀ : ℝ)
    (hE : 0 < E) (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) :
    let c : ℝ := (1 + q₀) ^ 2 / (4 * q₀)
    ∀ q : ℝ, q₀ ≤ q → q < 1 →
      NNBoundSq (c * (E ^ 2 * q / (1 - q) ^ 2))
        (c * (-(E ^ 3 * q * (1 + q)) / (1 - q) ^ 3)) := by
  dsimp only
  exact (scaledEuler_NN_cutoff_iff E q₀ ((1 + q₀) ^ 2 / (4 * q₀))
    hE hq₀ hq₀1 (by positivity)).2 le_rfl

/-- An explicit point below one defeats any proposed upper bound on the
multiplier threshold. -/
theorem eulerThreshold_gt_at_explicit_small_q (B : ℝ) :
    let q : ℝ := 1 / (8 * (|B| + 1))
    0 < q ∧ q < 1 ∧ B < (1 + q) ^ 2 / (4 * q) := by
  let q : ℝ := 1 / (8 * (|B| + 1))
  change 0 < q ∧ q < 1 ∧ B < (1 + q) ^ 2 / (4 * q)
  have hden : 0 < 8 * (|B| + 1) := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    apply (div_lt_iff₀ hden).2
    nlinarith [abs_nonneg B]
  have hqden : q * (8 * (|B| + 1)) = 1 := by
    dsimp [q]
    exact div_mul_cancel₀ 1 hden.ne'
  refine ⟨hq, hq1, (lt_div_iff₀ (mul_pos (by norm_num) hq)).2 ?_⟩
  have hBq : B * q ≤ |B| * q :=
    mul_le_mul_of_nonneg_right (le_abs_self B) hq.le
  nlinarith [sq_nonneg q]

/-- The exact multiplier threshold is unbounded on the open interval `(0, 1)`. -/
theorem eulerThreshold_unbounded (B : ℝ) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ B < (1 + q) ^ 2 / (4 * q) :=
  ⟨1 / (8 * (|B| + 1)), eulerThreshold_gt_at_explicit_small_q B⟩

/-- Every fixed positive multiplier fails at the stated explicit positive
point, independently of the positive energy. -/
theorem scaledEuler_NN_fails_at_explicit_small_q (E c : ℝ)
    (hE : 0 < E) (hc : 0 < c) :
    let q : ℝ := 1 / (8 * (|c| + 1))
    ¬ NNBoundSq (c * (E ^ 2 * q / (1 - q) ^ 2))
      (c * (-(E ^ 3 * q * (1 + q)) / (1 - q) ^ 3)) := by
  let q : ℝ := 1 / (8 * (|c| + 1))
  change ¬ NNBoundSq (c * (E ^ 2 * q / (1 - q) ^ 2))
    (c * (-(E ^ 3 * q * (1 + q)) / (1 - q) ^ 3))
  have hq := eulerThreshold_gt_at_explicit_small_q c
  change 0 < q ∧ q < 1 ∧ c < (1 + q) ^ 2 / (4 * q) at hq
  intro hNN
  have hcore := (scaledEuler_NN_iff E q c hE hq.1 hq.2.1 hc).1 hNN
  have hstrict := (lt_div_iff₀ (mul_pos (by norm_num) hq.1)).1 hq.2.2
  nlinarith

/-- A fixed positive multiplier cannot satisfy the Euler-mode NN slot bound
throughout `(0, 1)`. The conclusion does not rule out a fixed cutoff interval. -/
theorem not_scaledEuler_NN_uniform (E c : ℝ) (hE : 0 < E) (hc : 0 < c) :
    ¬ ∀ q : ℝ, 0 < q → q < 1 →
      NNBoundSq (c * (E ^ 2 * q / (1 - q) ^ 2))
        (c * (-(E ^ 3 * q * (1 + q)) / (1 - q) ^ 3)) := by
  intro h
  have hq := eulerThreshold_gt_at_explicit_small_q c
  exact scaledEuler_NN_fails_at_explicit_small_q E c hE hc
    (h (1 / (8 * (|c| + 1))) hq.1 hq.2.1)

end InfoGeometry.Arithmetic.SelfConcordantZetaBarrierProofs
