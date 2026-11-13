/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# A real porosity-loss recurrence

This is the geometric-loss recurrence obtained from equation (3.9) of
Knutsen, arXiv:2204.03068v1, after choosing geometric radii. Its arithmetic
does not assume an analytic sampling inequality. Those hypotheses belong to
the multiscale localization owner.
-/

noncomputable section
namespace InfoGeometry.Analysis.PorosityIteration

open Finset

/-- Remaining porosity after successive geometric losses. -/
def remainingPorosity (ν : ℝ) : ℕ → ℝ
  | 0 => ν
  | n + 1 => remainingPorosity ν n - (ν / 3) ^ (n + 1)

/-- The recurrence is exactly a finite geometric-loss sum. -/
theorem remainingPorosity_eq_sub_sum (ν : ℝ) (n : ℕ) :
    remainingPorosity ν n = ν - ∑ j ∈ range n, (ν / 3) ^ (j + 1) := by
  induction n with
  | zero => simp [remainingPorosity]
  | succ n ih =>
    rw [remainingPorosity, ih, sum_range_succ]
    ring

/-- A denominator-free closed form, valid for every real initial parameter. -/
theorem remainingPorosity_closed_form (ν : ℝ) (n : ℕ) :
    (3 - ν) * remainingPorosity ν n =
      ν * (2 - ν) + ν * (ν / 3) ^ n := by
  induction n with
  | zero => simp [remainingPorosity]; ring
  | succ n ih =>
    rw [remainingPorosity, mul_sub, ih, pow_succ]
    ring

/-- Each step removes a nonnegative quantity for nonnegative initial porosity. -/
theorem remainingPorosity_succ_le {ν : ℝ} (hν : 0 ≤ ν) (n : ℕ) :
    remainingPorosity ν (n + 1) ≤ remainingPorosity ν n := by
  rw [remainingPorosity]
  exact sub_le_self _ (pow_nonneg (div_nonneg hν (by norm_num)) _)

/-- Remaining porosity never exceeds the initial parameter. -/
theorem remainingPorosity_le_initial {ν : ℝ} (hν : 0 ≤ ν) (n : ℕ) :
    remainingPorosity ν n ≤ ν := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (remainingPorosity_succ_le hν n).trans ih

/-- The loss is uniformly at most one half of the initial porosity. -/
theorem half_le_remainingPorosity {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n : ℕ) :
    ν / 2 ≤ remainingPorosity ν n := by
  have hpow : 0 ≤ (ν / 3) ^ n := pow_nonneg (by positivity) _
  have hprod : 0 ≤ ν * (ν / 3) ^ n := mul_nonneg hν0 hpow
  have hbase : 0 ≤ ν * (1 - ν) := mul_nonneg hν0 (by linarith)
  have hid := remainingPorosity_closed_form ν n
  have hfactor : 0 < 3 - ν := by linarith
  nlinarith

theorem remainingPorosity_nonneg {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n : ℕ) :
    0 ≤ remainingPorosity ν n :=
  (div_nonneg hν0 (by norm_num)).trans (half_le_remainingPorosity hν0 hν1 n)

theorem remainingPorosity_pos {ν : ℝ}
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (n : ℕ) :
    0 < remainingPorosity ν n :=
  (half_pos hν0).trans_le (half_le_remainingPorosity hν0.le hν1 n)

/-- Uniform upper bound for the retained fraction at any nonnegative exponent. -/
theorem retainedFraction_le {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n exponent : ℕ) :
    1 - remainingPorosity ν n ^ exponent ≤ 1 - (ν / 2) ^ exponent := by
  have hpow : (ν / 2) ^ exponent ≤ remainingPorosity ν n ^ exponent := by
    gcongr
    exact half_le_remainingPorosity hν0 hν1 n
  linarith

/-- The retained fraction stays nonnegative under the unit-interval hypotheses. -/
theorem retainedFraction_nonneg {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n exponent : ℕ) :
    0 ≤ 1 - remainingPorosity ν n ^ exponent := by
  have hpow : remainingPorosity ν n ^ exponent ≤ (1 : ℝ) ^ exponent := by
    gcongr
    · exact remainingPorosity_nonneg hν0 hν1 n
    · exact (remainingPorosity_le_initial hν0 n).trans hν1
  simpa only [one_pow] using sub_nonneg.mpr hpow

/-- Positive porosity and positive dimension give a strict uniform retained fraction. -/
theorem uniformRetainedFraction_mem_Ioo {ν : ℝ}
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) {d : ℕ} (hd : 0 < d) :
    1 - (ν / 2) ^ (2 * d) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hhalf : 0 < ν / 2 := half_pos hν0
  have hpowpos : 0 < (ν / 2) ^ (2 * d) := pow_pos hhalf _
  have hexponent : 0 < 2 * d := Nat.mul_pos (by decide) hd
  have hpowlt : (ν / 2) ^ (2 * d) < 1 := by
    exact pow_lt_one₀ hhalf.le (by linarith) (Nat.ne_zero_of_lt hexponent)
  constructor <;> linarith

end InfoGeometry.Analysis.PorosityIteration
