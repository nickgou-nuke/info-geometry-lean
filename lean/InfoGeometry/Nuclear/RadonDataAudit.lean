/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact arithmetic for the nine-cartridge radon draft

The finite data below transcribe the embedded CSV in
`Pasted text(20261118-075647).txt`. Index `0` denotes cartridge 1.
The certificates concern these entered numbers, not the correctness of the
measurements or a statistical model. No daughter equilibrium, detector
calibration, error bars, or fitted attenuation coefficient is inferred.

The real-valued correction is the start-time exponential convention used in
that draft. Finite acquisition averaging requires an additional model.
-/

namespace InfoGeometry.Nuclear.RadonDataAudit

/-- Transcribed net peak areas at 609 keV, in cartridge order. -/
def counts609 : Fin 9 → ℕ :=
  ![155028, 112751, 56385, 34000, 17414, 8689, 4336, 2272, 1392]

/-- Transcribed net peak areas at 352 keV, in cartridge order. -/
def counts352 : Fin 9 → ℕ :=
  ![243750, 177341, 89796, 52368, 27324, 13440, 6777, 3516, 2417]

/-- Reported live time, common to every listed spectrum, in seconds. -/
def liveSeconds : ℕ := 900

/-- Reported elapsed start times relative to cartridge 9, in seconds. -/
def elapsedSeconds : Fin 9 → ℕ :=
  ![7753, 6759, 5797, 4840, 3891, 2928, 1983, 1034, 0]

/-- Recorded clock readings, expressed as seconds after midnight. -/
def startSeconds : Fin 9 → ℕ :=
  ![12 * 3600 + 25 * 60 + 47, 12 * 3600 + 9 * 60 + 13,
    11 * 3600 + 53 * 60 + 11, 11 * 3600 + 37 * 60 + 14,
    11 * 3600 + 21 * 60 + 25, 11 * 3600 + 5 * 60 + 22,
    10 * 3600 + 49 * 60 + 37, 10 * 3600 + 33 * 60 + 48,
    10 * 3600 + 16 * 60 + 34]

/-- Every entered elapsed time agrees with the recorded start times. -/
theorem elapsedSeconds_eq_start_sub (i : Fin 9) :
    elapsedSeconds i = startSeconds i - startSeconds 8 := by
  fin_cases i <;> norm_num [elapsedSeconds, startSeconds]

/-- Rational ratio of entered peak areas from the same cartridge. -/
def peakRatio (i : Fin 9) : ℚ := (counts352 i : ℚ) / counts609 i

/-- Raw 609 keV rate ratios equal count ratios because live times agree. -/
theorem raw_ratio_three_four :
    ((counts609 2 : ℚ) / liveSeconds) /
      ((counts609 3 : ℚ) / liveSeconds) = 11277 / 6800 := by
  norm_num [counts609, liveSeconds]

/-- The entered raw rates do not halve between cartridges 3 and 4. -/
theorem raw_ratio_three_four_ne_two :
    ((counts609 2 : ℚ) / liveSeconds) /
      ((counts609 3 : ℚ) / liveSeconds) ≠ 2 := by
  rw [raw_ratio_three_four]
  norm_num

/-- Cartridge 3 lies above the stated descriptive interval's upper endpoint. -/
theorem peakRatio_three_gt_158 : (79 / 50 : ℚ) < peakRatio 2 := by
  norm_num [peakRatio, counts352, counts609]

/-- Cartridge 9's entered peak ratio exceeds 1.7. -/
theorem peakRatio_nine_gt_17 : (17 / 10 : ℚ) < peakRatio 8 := by
  norm_num [peakRatio, counts352, counts609]

theorem peakRatio_three_ne_nine : peakRatio 2 ≠ peakRatio 8 := by
  norm_num [peakRatio, counts352, counts609]

theorem peakRatio_one_ne_three : peakRatio 0 ≠ peakRatio 2 := by
  norm_num [peakRatio, counts352, counts609]

/-- Even within cartridges 1–8, the entered peak ratios are not exactly constant.
This does not test statistical compatibility within measurement uncertainties. -/
theorem peakRatio_first_eight_not_constant :
    ¬ ∃ q : ℚ, ∀ i : Fin 8, peakRatio i.castSucc = q := by
  rintro ⟨q, hq⟩
  exact peakRatio_one_ne_three ((hq 0).trans (hq 2).symm)

/-- Exact constancy of all nine entered peak ratios is refuted. -/
theorem peakRatio_not_constant : ¬ ∃ q : ℚ, ∀ i, peakRatio i = q := by
  rintro ⟨q, hq⟩
  exact peakRatio_three_ne_nine ((hq 2).trans (hq 8).symm)

noncomputable section

/-- Start-time correction of a count rate to a reference elapsed time. -/
def correctedRate (lambda elapsed counts live : ℝ) : ℝ :=
  (counts / live) * Real.exp (lambda * elapsed)

theorem correctedRate_pos (lambda elapsed : ℝ) {counts live : ℝ}
    (hcounts : 0 < counts) (hlive : 0 < live) :
    0 < correctedRate lambda elapsed counts live := by
  exact mul_pos (div_pos hcounts hlive) (Real.exp_pos _)

theorem correctedRate_ne_zero (lambda elapsed : ℝ) {counts live : ℝ}
    (hcounts : counts ≠ 0) (hlive : live ≠ 0) :
    correctedRate lambda elapsed counts live ≠ 0 := by
  exact mul_ne_zero (div_ne_zero hcounts hlive) (Real.exp_ne_zero _)

@[simp] theorem correctedRate_zero_elapsed (lambda counts live : ℝ) :
    correctedRate lambda 0 counts live = counts / live := by
  simp [correctedRate]

/-- A common correction and a common nonzero live time cancel in a line ratio.
The algebraic identity also holds for zero denominator counts under Lean's
total division; `correctedRate_ne_zero` gives the usual nonzero case. -/
theorem correctedRate_line_ratio (lambda elapsed numerator denominator live : ℝ)
    (hlive : live ≠ 0) :
    correctedRate lambda elapsed numerator live /
      correctedRate lambda elapsed denominator live = numerator / denominator := by
  unfold correctedRate
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero _)]
  exact div_div_div_cancel_right₀ hlive numerator denominator

/-- Increasing elapsed time multiplies the correction by the corresponding
exponential factor. -/
theorem correctedRate_elapsed_add (lambda elapsed shift counts live : ℝ) :
    correctedRate lambda (elapsed + shift) counts live =
      correctedRate lambda elapsed counts live * Real.exp (lambda * shift) := by
  simp only [correctedRate, mul_add, Real.exp_add, mul_assoc]

/-- Moving the reference time forward subtracts the same shift from elapsed
times and scales all corrected rates by the same positive factor. -/
theorem correctedRate_reference_shift (lambda elapsed shift counts live : ℝ) :
    correctedRate lambda (elapsed - shift) counts live =
      correctedRate lambda elapsed counts live * Real.exp (-(lambda * shift)) := by
  simp only [correctedRate, mul_sub, Real.exp_sub, Real.exp_neg,
    div_eq_mul_inv, mul_assoc]

/-- Changing a common reference time leaves ratios of corrected rates invariant,
even when the spectra have different elapsed and live times. -/
theorem correctedRate_ratio_reference_shift
    (lambda elapsed₁ elapsed₂ shift counts₁ counts₂ live₁ live₂ : ℝ) :
    correctedRate lambda (elapsed₁ - shift) counts₁ live₁ /
        correctedRate lambda (elapsed₂ - shift) counts₂ live₂ =
      correctedRate lambda elapsed₁ counts₁ live₁ /
        correctedRate lambda elapsed₂ counts₂ live₂ := by
  rw [correctedRate_reference_shift, correctedRate_reference_shift]
  exact mul_div_mul_right _ _ (Real.exp_ne_zero _)

/-- Applying the reverse exponential removes the start-time correction. -/
theorem correctedRate_roundtrip (lambda elapsed counts live : ℝ) :
    correctedRate lambda elapsed counts live * Real.exp (-(lambda * elapsed)) =
      counts / live := by
  rw [correctedRate, mul_assoc, ← Real.exp_add]
  simp

/-- The source's correction applied to the two lines of one cartridge. -/
def correctedPeakRatio (lambda : ℝ) (i : Fin 9) : ℝ :=
  correctedRate lambda (elapsedSeconds i) (counts352 i) liveSeconds /
    correctedRate lambda (elapsedSeconds i) (counts609 i) liveSeconds

theorem correctedPeakRatio_eq (lambda : ℝ) (i : Fin 9) :
    correctedPeakRatio lambda i = (counts352 i : ℝ) / counts609 i := by
  unfold correctedPeakRatio
  apply correctedRate_line_ratio
  norm_num [liveSeconds]

/-- No choice of a common exponential correction brings cartridge 3's entered
line ratio below the upper endpoint 1.58. -/
theorem correctedPeakRatio_three_gt_158 (lambda : ℝ) :
    (79 / 50 : ℝ) < correctedPeakRatio lambda 2 := by
  rw [correctedPeakRatio_eq]
  norm_num [counts352, counts609]

end

end InfoGeometry.Nuclear.RadonDataAudit
