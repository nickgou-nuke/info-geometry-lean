/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The positive logarithmic divided difference as a resolvent integral

This is the scalar integration lemma for a two-sheet operator resolvent.
The ambient operator identity must be proved separately before applying it.
The coefficient is the inverse logarithmic mean, including its nonzero
equal-weight value; it is not the forward Kubo--Mori logarithmic mean.
-/

noncomputable section

namespace InfoGeometry.Analysis

open Filter MeasureTheory Set
open scoped Topology

/-- The logarithmic divided difference, with the derivative value on the diagonal. -/
def logDividedDifference (p q : ℝ) : ℝ :=
  if p = q then p⁻¹ else (Real.log p - Real.log q) / (p - q)

@[simp] theorem logDividedDifference_self (p : ℝ) :
    logDividedDifference p p = p⁻¹ := by
  simp [logDividedDifference]

theorem logDividedDifference_symm (p q : ℝ) :
    logDividedDifference p q = logDividedDifference q p := by
  by_cases hpq : p = q
  · subst q
    rfl
  · simp only [logDividedDifference, ite_eq_right hpq, ite_eq_right (Ne.symm hpq)]
    rw [show Real.log q - Real.log p = -(Real.log p - Real.log q) by ring,
      show q - p = -(p - q) by ring, neg_div_neg_eq]

theorem logDividedDifference_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    0 < logDividedDifference p q := by
  by_cases hpq : p = q
  · simp only [logDividedDifference, ite_eq_left hpq]
    exact inv_pos.mpr hp
  · rw [logDividedDifference, ite_eq_right hpq]
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact div_pos_of_neg_of_neg
        (sub_neg.mpr (Real.log_lt_log hp hlt)) (sub_neg.mpr hlt)
    · exact div_pos
        (sub_pos.mpr (Real.log_lt_log hq hgt)) (sub_pos.mpr hgt)

private def logResolventPrimitive (p q s : ℝ) : ℝ :=
  if p = q then -(p + s)⁻¹
  else (Real.log (p + s) - Real.log (q + s)) / (q - p)

private theorem hasDerivAt_logResolventPrimitive {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (logResolventPrimitive p q)
      (1 / ((p + s) * (q + s))) s := by
  change HasDerivAt
    (fun t : ℝ => if p = q then -(p + t)⁻¹
      else (Real.log (p + t) - Real.log (q + t)) / (q - p))
    (1 / ((p + s) * (q + s))) s
  have hpz : p + s ≠ 0 := (add_pos_of_pos_of_nonneg hp hs).ne'
  have hqz : q + s ≠ 0 := (add_pos_of_pos_of_nonneg hq hs).ne'
  by_cases hpq : p = q
  · subst q
    have hder := (((hasDerivAt_id s).const_add p).inv hpz).neg
    change HasDerivAt (fun t : ℝ => -(p + t)⁻¹)
      (-(-1 / (p + s) ^ 2)) s at hder
    have hvalue : -(-1 / (p + s) ^ 2) = 1 / ((p + s) * (p + s)) := by
      rw [neg_div, neg_neg, pow_two]
    rw [hvalue] at hder
    simpa only [ite_eq_left (show p = p from rfl), ite_true] using hder
  · have hqp : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
    have hder := ((((hasDerivAt_id s).const_add p).log hpz).sub
      (((hasDerivAt_id s).const_add q).log hqz)).div_const (q - p)
    change HasDerivAt
      (fun t : ℝ => (Real.log (p + t) - Real.log (q + t)) / (q - p))
      ((1 / (p + s) - 1 / (q + s)) / (q - p)) s at hder
    have hvalue :
        (1 / (p + s) - 1 / (q + s)) / (q - p) =
          1 / ((p + s) * (q + s)) := by
      field_simp [hpz, hqz, hqp]
      ring
    simpa only [ite_eq_right hpq, hvalue] using hder

private theorem tendsto_logResolventPrimitive {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) :
    Tendsto (logResolventPrimitive p q) atTop (𝓝 0) := by
  change Tendsto
    (fun s : ℝ => if p = q then -(p + s)⁻¹
      else (Real.log (p + s) - Real.log (q + s)) / (q - p)) atTop (𝓝 0)
  have hinv (a : ℝ) :
      Tendsto (fun s : ℝ => (a + s)⁻¹) atTop (𝓝 0) := by
    simpa only [one_mul, add_comm] using
      tendsto_mul_add_inv_atTop_nhds_zero (1 : ℝ) a one_ne_zero
  by_cases hpq : p = q
  · simpa only [ite_eq_left hpq, neg_zero] using (hinv p).neg
  · have hratio :
        Tendsto (fun s : ℝ => (p + s) / (q + s)) atTop (𝓝 1) := by
      have hbase :
          Tendsto (fun s : ℝ => 1 + (p - q) * (q + s)⁻¹) atTop (𝓝 1) := by
        simpa using ((hinv q).const_mul (p - q)).const_add 1
      refine hbase.congr' ?_
      filter_upwards [Ici_mem_atTop (0 : ℝ)] with s hs
      have hqz : q + s ≠ 0 := (add_pos_of_pos_of_nonneg hq hs).ne'
      field_simp [hqz]
      ring
    have hdiff : Tendsto
        (fun s : ℝ => Real.log (p + s) - Real.log (q + s)) atTop (𝓝 0) := by
      have hlog : Tendsto
          (fun s : ℝ => Real.log ((p + s) / (q + s))) atTop (𝓝 0) := by
        simpa using hratio.log one_ne_zero
      refine hlog.congr' ?_
      filter_upwards [Ici_mem_atTop (0 : ℝ)] with s hs
      exact Real.log_div (add_pos_of_pos_of_nonneg hp hs).ne'
        (add_pos_of_pos_of_nonneg hq hs).ne'
    simpa only [ite_eq_right hpq, zero_div] using
      hdiff.div_const (q - p)

/-- Absolute integrability of the two positive spectral resolvent factors. -/
theorem integrableOn_Ioi_logResolventKernel {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ => 1 / ((p + s) * (q + s))) (Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun s hs => hasDerivAt_logResolventPrimitive hp hq s hs)
    (fun s hs => le_of_lt (one_div_pos.mpr (mul_pos (add_pos hp hs) (add_pos hq hs))))
    (tendsto_logResolventPrimitive hp hq)

/-- The resolvent integral is the logarithmic divided difference, including equal weights. -/
theorem integral_Ioi_logResolventKernel {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ), 1 / ((p + s) * (q + s))) =
      logDividedDifference p q := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s hs => hasDerivAt_logResolventPrimitive hp hq s hs)
    (integrableOn_Ioi_logResolventKernel hp hq)
    (tendsto_logResolventPrimitive hp hq)]
  unfold logResolventPrimitive logDividedDifference
  split_ifs with hpq
  · simp
  · simp only [add_zero, zero_sub]
    rw [show q - p = -(p - q) by ring, div_neg, neg_neg]

end InfoGeometry.Analysis
