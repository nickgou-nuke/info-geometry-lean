/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.SelfConcordantZetaBarrierProofs

/-! Exact scaling criterion for the convex Euler-mode derivative slots.
This is an algebraic NN inequality, not a zeta or infinite-product theorem. -/
namespace InfoGeometry.Arithmetic.SelfConcordantZetaBarrierProofs

theorem scaledEuler_NN_iff (E q c : ℝ)
    (hE : 0 < E) (hq : 0 < q) (hq1 : q < 1) (hc : 0 < c) :
    NNBoundSq (c * (E ^ 2 * q / (1 - q) ^ 2))
      (c * (-(E ^ 3 * q * (1 + q)) / (1 - q) ^ 3)) ↔
        (1 + q) ^ 2 ≤ 4 * c * q := by
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  have hf : 0 < c ^ 2 * E ^ 6 * q ^ 2 / (1 - q) ^ 6 := by positivity
  have heq :
      4 * (c * (E ^ 2 * q / (1 - q) ^ 2)) ^ 3 -
        (c * (-(E ^ 3 * q * (1 + q)) / (1 - q) ^ 3)) ^ 2 =
      (c ^ 2 * E ^ 6 * q ^ 2 / (1 - q) ^ 6) *
        (4 * c * q - (1 + q) ^ 2) := by
    field_simp [ne_of_gt hd]
  unfold NNBoundSq
  have hsecond : 0 ≤ c * (E ^ 2 * q / (1 - q) ^ 2) := by positivity
  rw [and_iff_right hsecond, ← sub_nonneg, heq,
    mul_nonneg_iff_of_pos_left hf, sub_nonneg]

/-- The cutoff threshold decreases on the positive interval below one. -/
theorem eulerThreshold_antitone (q₀ q : ℝ)
    (hq₀ : 0 < q₀) (hle : q₀ ≤ q) (hq1 : q < 1) :
    (1 + q) ^ 2 / (4 * q) ≤ (1 + q₀) ^ 2 / (4 * q₀) := by
  have hq : 0 < q := lt_of_lt_of_le hq₀ hle
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * q)
    (by positivity : 0 < 4 * q₀)).2
  have hp : 0 ≤ (q - q₀) * (1 - q₀ * q) := by
    apply mul_nonneg (sub_nonneg.mpr hle)
    have hq₀1 : q₀ < 1 := lt_of_le_of_lt hle hq1
    have hprod : q₀ * q < 1 := calc
      q₀ * q ≤ 1 * q := mul_le_mul_of_nonneg_right hq₀1.le hq.le
      _ < 1 := by simpa using hq1
    linarith
  nlinarith

/-- A single cutoff scale supplies the NN slot inequality on the whole interval. -/
theorem scaledEuler_NN_on_cutoff (E q₀ q c : ℝ)
    (hE : 0 < E) (hq₀ : 0 < q₀) (hle : q₀ ≤ q) (hq1 : q < 1)
    (hc : (1 + q₀) ^ 2 / (4 * q₀) ≤ c) :
    NNBoundSq (c * (E ^ 2 * q / (1 - q) ^ 2))
      (c * (-(E ^ 3 * q * (1 + q)) / (1 - q) ^ 3)) := by
  have hq : 0 < q := lt_of_lt_of_le hq₀ hle
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hc
  apply (scaledEuler_NN_iff E q c hE hq hq1 hcpos).2
  have ht := le_trans (eulerThreshold_antitone q₀ q hq₀ hle hq1) hc
  have h := (div_le_iff₀ (by positivity : 0 < 4 * q)).1 ht
  nlinarith

/-- On a nonempty cutoff interval the endpoint threshold is also necessary. -/
theorem scaledEuler_NN_cutoff_iff (E q₀ c : ℝ)
    (hE : 0 < E) (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) (hc : 0 < c) :
    (∀ q : ℝ, q₀ ≤ q → q < 1 →
      NNBoundSq (c * (E ^ 2 * q / (1 - q) ^ 2))
        (c * (-(E ^ 3 * q * (1 + q)) / (1 - q) ^ 3))) ↔
      (1 + q₀) ^ 2 / (4 * q₀) ≤ c := by
  constructor
  · intro h
    have ht := (scaledEuler_NN_iff E q₀ c hE hq₀ hq₀1 hc).1
      (h q₀ le_rfl hq₀1)
    apply (div_le_iff₀ (by positivity : 0 < 4 * q₀)).2
    nlinarith
  · intro h q hle hq1
    exact scaledEuler_NN_on_cutoff E q₀ q c hE hq₀ hle hq1 h

end InfoGeometry.Arithmetic.SelfConcordantZetaBarrierProofs
