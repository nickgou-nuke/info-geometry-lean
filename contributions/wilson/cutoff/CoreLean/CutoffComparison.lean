/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-!
# Normalized consecutive-cutoff comparisons

The physical partition function stays in the denominator. The numerator may
already include the perimeter/corner normalization of the observable. Relative
numerator and denominator errors, together with a bound on the new normalized
observable, give the increment estimate used in Section 11 of
`WILSON_LOOPS_CONTINUUM_LIMIT.tex`.

The final theorem derives full-sequence convergence and a quantitative tail
bound. Its hypotheses are estimates to be supplied by the RG construction;
this file does not assert those estimates for the Wilson measure.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace CoreLean.CutoffComparison

/-- Exact difference identity, retaining the old physical denominator. -/
theorem normalized_sub (N N' Z Z' : ℂ) (hZ : Z ≠ 0) (hZ' : Z' ≠ 0) :
    N' / Z' - N / Z = ((N' - N) - (N' / Z') * (Z' - Z)) / Z := by
  field_simp [hZ, hZ']
  ring

/-- Relative errors in the numerator and partition function control the
normalized expectation. No absolute lower bound uniform in the cutoff is
needed: both errors are measured relative to the same positive denominator. -/
theorem norm_normalized_sub_le (N N' : ℂ) {Z Z' B εN εZ : ℝ}
    (hZ : 0 < Z) (hZ' : 0 < Z') (hB : 0 ≤ B)
    (hN : ‖N' - N‖ ≤ εN * Z)
    (hPartition : |Z' - Z| ≤ εZ * Z)
    (hNormalized : ‖N' / (Z' : ℂ)‖ ≤ B) :
    ‖N' / (Z' : ℂ) - N / (Z : ℂ)‖ ≤ εN + B * εZ := by
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hZc' : (Z' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ'.ne'
  rw [normalized_sub N N' (Z : ℂ) (Z' : ℂ) hZc hZc', norm_div,
    Complex.norm_real, Real.norm_of_nonneg hZ.le]
  apply (div_le_iff₀ hZ).2
  calc
    ‖(N' - N) - N' / (Z' : ℂ) * ((Z' : ℂ) - Z)‖
        ≤ ‖N' - N‖ + ‖N' / (Z' : ℂ) * ((Z' : ℂ) - Z)‖ := norm_sub_le _ _
    _ = ‖N' - N‖ + ‖N' / (Z' : ℂ)‖ * |Z' - Z| := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ εN * Z + B * (εZ * Z) := by
      exact add_le_add hN
        (mul_le_mul hNormalized hPartition (abs_nonneg _) hB)
    _ = (εN + B * εZ) * Z := by ring

/-- A complex scalar normalization changes a bounded observable by an
explicit exponential error. This accounts for swapping loop constants. -/
theorem norm_exp_mul_sub_le (z w : ℂ) {δ B : ℝ}
    (hz : ‖z‖ ≤ δ) (hw : ‖w‖ ≤ B) :
    ‖Complex.exp z * w - w‖ ≤ (Real.exp δ - 1) * B := by
  rw [show Complex.exp z * w - w = (Complex.exp z - 1) * w by ring, norm_mul]
  have hδ : 0 ≤ δ := (norm_nonneg z).trans hz
  have hexp : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
    simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1
  have he : ‖Complex.exp z - 1‖ ≤ Real.exp δ - 1 := by
    exact hexp.trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hz) 1)
  exact mul_le_mul he hw (norm_nonneg _) (sub_nonneg.mpr (Real.one_le_exp hδ))

/-- Summable relative numerator/denominator errors give a full cutoff limit
and its tail estimate, starting at any fixed admissible cutoff `K₀`. -/
theorem exists_limit_of_relative_errors
    (N : ℕ → ℂ) (Z εN εZ : ℕ → ℝ) (K₀ : ℕ) {B : ℝ}
    (hZ : ∀ k, 0 < Z (K₀ + k)) (hB : 0 ≤ B)
    (hN : ∀ k, ‖N (K₀ + (k + 1)) - N (K₀ + k)‖ ≤ εN k * Z (K₀ + k))
    (hPartition : ∀ k, |Z (K₀ + (k + 1)) - Z (K₀ + k)| ≤ εZ k * Z (K₀ + k))
    (hNormalized : ∀ k, ‖N (K₀ + (k + 1)) / (Z (K₀ + (k + 1)) : ℂ)‖ ≤ B)
    (hsN : Summable εN) (hsZ : Summable εZ) :
    ∃ limit : ℂ,
      Tendsto (fun k => N k / (Z k : ℂ)) atTop (𝓝 limit) ∧
      ∀ k, ‖N (K₀ + k) / (Z (K₀ + k) : ℂ) - limit‖ ≤
        ∑' j, (εN (k + j) + B * εZ (k + j)) := by
  let F : ℕ → ℂ := fun k => N (K₀ + k) / (Z (K₀ + k) : ℂ)
  let e : ℕ → ℝ := fun k => εN k + B * εZ k
  have he : Summable e := hsN.add (hsZ.mul_left B)
  have hstep : ∀ k, dist (F k) (F (k + 1)) ≤ e k := by
    intro k
    rw [dist_comm, dist_eq_norm]
    exact norm_normalized_sub_le _ _ (hZ k) (hZ (k + 1)) hB
      (hN k) (hPartition k) (hNormalized k)
  obtain ⟨limit, hlimit⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable e hstep he)
  refine ⟨limit, ?_, fun k => ?_⟩
  · apply (tendsto_add_atTop_iff_nat K₀).mp
    simpa only [F, Nat.add_comm] using hlimit
  · exact (dist_eq_norm (F k) limit) ▸
      dist_le_tsum_of_dist_le_of_tendsto e hstep he hlimit k

end CoreLean.CutoffComparison
