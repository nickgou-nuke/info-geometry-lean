/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11LorentzAction
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith

/-!
# Positive operator norm bounds for real hyperbolic Peirce corners

The existing `modularAdjointFlow` is conjugation by a real hyperbolic channel
boost. Its name does not identify it with the Tomita--Takesaki automorphism
group of a specified state or weight. This file derives positive operator norm
identities from the existing exact corner-scaling theorems.

The repository convention is `P+ = (1 + eps) / 2` and
`uPlus A = P+ * A * P-`. This corner has weight `exp (2 * t)` and is
contractive precisely for `t ≤ 0` when it is nonzero. The opposite corner has
weight `exp (-2 * t)` and is contractive precisely for `0 ≤ t`.

Each finite-time flow remains invertible. Restriction to a contractive
half-line alone neither proves irreversible evolution nor constructs Hardy
spaces, resonance states, or a modular/KMS identification.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11LorentzCornerBounds

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.KKTLorentzOrbitBridge
open InfoGeometry.Canonical.Cl11LorentzAction
open InfoGeometry.Quantum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

/-- Exact positive operator norm on the corner with boost weight `+2`. -/
theorem norm_modularAdjointFlow_uPlus
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    ‖modularAdjointFlow X t (uPlus X A)‖ =
      Real.exp (2 * t) * ‖uPlus X A‖ := by
  rw [modularAdjointFlow_scales_uPlus, norm_smul,
    Real.norm_of_nonneg (Real.exp_nonneg _)]

/-- Exact positive operator norm on the corner with boost weight `-2`. -/
theorem norm_modularAdjointFlow_uMinus
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    ‖modularAdjointFlow X t (uMinus X A)‖ =
      Real.exp (-2 * t) * ‖uMinus X A‖ := by
  rw [modularAdjointFlow_scales_uMinus, norm_smul,
    Real.norm_of_nonneg (Real.exp_nonneg _)]

/-- A nonzero `uPlus` corner is contractive exactly on the nonpositive half-line. -/
theorem norm_modularAdjointFlow_uPlus_le_iff
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH)
    (hA : uPlus X A ≠ 0) :
    ‖modularAdjointFlow X t (uPlus X A)‖ ≤ ‖uPlus X A‖ ↔ t ≤ 0 := by
  rw [norm_modularAdjointFlow_uPlus]
  have hn : 0 < ‖uPlus X A‖ := norm_pos_iff.mpr hA
  have hscale :
      Real.exp (2 * t) * ‖uPlus X A‖ ≤ ‖uPlus X A‖ ↔
        Real.exp (2 * t) ≤ 1 := by
    simpa only [one_mul] using
      (mul_le_mul_iff_left₀ hn :
        Real.exp (2 * t) * ‖uPlus X A‖ ≤ 1 * ‖uPlus X A‖ ↔
          Real.exp (2 * t) ≤ 1)
  rw [hscale, Real.exp_le_one_iff]
  constructor <;> intro ht <;> linarith

/-- A nonzero `uMinus` corner is contractive exactly on the nonnegative half-line. -/
theorem norm_modularAdjointFlow_uMinus_le_iff
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH)
    (hA : uMinus X A ≠ 0) :
    ‖modularAdjointFlow X t (uMinus X A)‖ ≤ ‖uMinus X A‖ ↔ 0 ≤ t := by
  rw [norm_modularAdjointFlow_uMinus]
  have hn : 0 < ‖uMinus X A‖ := norm_pos_iff.mpr hA
  have hscale :
      Real.exp (-2 * t) * ‖uMinus X A‖ ≤ ‖uMinus X A‖ ↔
        Real.exp (-2 * t) ≤ 1 := by
    simpa only [one_mul] using
      (mul_le_mul_iff_left₀ hn :
        Real.exp (-2 * t) * ‖uMinus X A‖ ≤ 1 * ‖uMinus X A‖ ↔
          Real.exp (-2 * t) ≤ 1)
  rw [hscale, Real.exp_le_one_iff]
  constructor <;> intro ht <;> linarith

/-- The norm of a nonzero expanding corner is preserved only at zero rapidity. -/
theorem norm_modularAdjointFlow_uPlus_eq_iff
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH)
    (hA : uPlus X A ≠ 0) :
    ‖modularAdjointFlow X t (uPlus X A)‖ = ‖uPlus X A‖ ↔ t = 0 := by
  rw [norm_modularAdjointFlow_uPlus]
  have hn : 0 < ‖uPlus X A‖ := norm_pos_iff.mpr hA
  constructor
  · intro h
    have he : Real.exp (2 * t) = 1 := by
      apply mul_right_cancel₀ (ne_of_gt hn)
      simpa only [one_mul] using h
    have ht := (Real.exp_eq_one_iff (2 * t)).mp he
    linarith
  · rintro rfl
    simp

/-- The norm of a nonzero contracting corner is preserved only at zero rapidity. -/
theorem norm_modularAdjointFlow_uMinus_eq_iff
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH)
    (hA : uMinus X A ≠ 0) :
    ‖modularAdjointFlow X t (uMinus X A)‖ = ‖uMinus X A‖ ↔ t = 0 := by
  rw [norm_modularAdjointFlow_uMinus]
  have hn : 0 < ‖uMinus X A‖ := norm_pos_iff.mpr hA
  constructor
  · intro h
    have he : Real.exp (-2 * t) = 1 := by
      apply mul_right_cancel₀ (ne_of_gt hn)
      simpa only [one_mul] using h
    have ht := (Real.exp_eq_one_iff (-2 * t)).mp he
    linarith
  · rintro rfl
    simp

/-- Positive norm growth does not remove the existing inverse at finite time. -/
theorem modularAdjointFlow_neg_apply
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    modularAdjointFlow X (-t) (modularAdjointFlow X t A) = A := by
  rw [← modularAdjointFlow_add, neg_add_cancel]
  simp [modularAdjointFlow, modularFlow, channelBoost, ← ContinuousLinearMap.one_def]

end InfoGeometry.Canonical.Cl11LorentzCornerBounds
