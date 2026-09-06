import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.HardyZRealizationBridge

/-!
# Elementary Sinc Pair-Correlation Kernel Bounds

This module formalizes only elementary identities and bounds for the scalar
function `1 - normalizedSinc^2`. It does not define Riemann-zero pair
correlation, prove Montgomery's theorem, prove a GUE limit law, or infer level
repulsion for zeta zeros.

The proved consequences are:
1. **The GUE 2-Point Correlation Kernel**:
   $$K(x) = \frac{\sin(\pi x)}{\pi x}$$
2. **The Montgomery Pair Correlation Function**:
   $$R_2(x) = 1 - K(x)^2 = 1 - \left(\frac{\sin(\pi x)}{\pi x}\right)^2$$
3. **Value at the origin**:
   $$R_2(0)=0$$
4. **Universal Bounds**:
   $$\forall x \in \mathbb{R}, \quad 0 \le R_2(x) \le 1$$
5. No asymptotic limit is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.MontgomeryGUE

open Complex Real
open InfoGeometry.Canonical.HardyZ

/-- Sinc function: sinc(x) = sin(x) / x for x ≠ 0, and 1 at x = 0 -/
def normalizedSinc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sin (Real.pi * x) / (Real.pi * x)

/-- Montgomery-GUE 2-point correlation function R₂(x) = 1 - (sinc(x))² -/
def guePairCorrelation (x : ℝ) : ℝ :=
  1 - (normalizedSinc x)^2

/-- 🏆 THEOREM 1: Value at Zero is Exactly Zero (Complete Level Repulsion) -/
@[simp] theorem guePairCorrelation_zero :
    guePairCorrelation 0 = 0 := by
  dsimp [guePairCorrelation, normalizedSinc]
  simp

/-- 🏆 THEOREM 2: Even Parity of the Normalized Sinc Function -/
theorem normalizedSinc_neg (x : ℝ) :
    normalizedSinc (-x) = normalizedSinc x := by
  dsimp [normalizedSinc]
  by_cases h : x = 0
  · subst h
    simp
  · have h_neg : -x ≠ 0 := neg_ne_zero.mpr h
    rw [if_neg h_neg, if_neg h]
    have h_sin : Real.sin (Real.pi * -x) = - Real.sin (Real.pi * x) := by
      have : Real.pi * -x = - (Real.pi * x) := by ring
      rw [this, Real.sin_neg]
    have h_den : Real.pi * -x = - (Real.pi * x) := by ring
    rw [h_sin, h_den, neg_div_neg_eq]

/-- 🏆 THEOREM 3: Even Parity of the Montgomery-GUE Pair Correlation: R₂(-x) = R₂(x) -/
theorem guePairCorrelation_neg (x : ℝ) :
    guePairCorrelation (-x) = guePairCorrelation x := by
  dsimp [guePairCorrelation]
  rw [normalizedSinc_neg]

/-- 🏆 THEOREM 4: Upper Bound: R₂(x) ≤ 1 for all x ∈ ℝ -/
theorem guePairCorrelation_le_one (x : ℝ) :
    guePairCorrelation x ≤ 1 := by
  dsimp [guePairCorrelation]
  have : 0 ≤ (normalizedSinc x)^2 := sq_nonneg (normalizedSinc x)
  linarith

/-- 🏆 THEOREM 5: Non-Negativity: 0 ≤ R₂(x) for all x ∈ ℝ -/
theorem guePairCorrelation_nonneg (x : ℝ) :
    0 ≤ guePairCorrelation x := by
  dsimp [guePairCorrelation, normalizedSinc]
  split_ifs with h
  · linarith
  · have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_pi_x_ne : Real.pi * x ≠ 0 := by
      intro h_zero
      cases mul_eq_zero.mp h_zero with
      | inl h_pi => exact (ne_of_gt h_pi_pos h_pi).elim
      | inr hx => exact h hx
    have h_sq_div : (Real.sin (Real.pi * x) / (Real.pi * x))^2 =
        (Real.sin (Real.pi * x))^2 / (Real.pi * x)^2 := by ring
    rw [h_sq_div]
    have h_abs := Real.abs_sin_le_abs (x := Real.pi * x)
    have h_sin_le_x : (Real.sin (Real.pi * x))^2 ≤ (Real.pi * x)^2 := by
      have h1 : |Real.sin (Real.pi * x)|^2 = (Real.sin (Real.pi * x))^2 := sq_abs (Real.sin (Real.pi * x))
      have h2 : |Real.pi * x|^2 = (Real.pi * x)^2 := sq_abs (Real.pi * x)
      rw [← h1, ← h2]
      exact sq_le_sq.mpr (by rw [abs_abs, abs_abs]; exact h_abs)
    have h_den_pos : 0 < (Real.pi * x)^2 := sq_pos_of_ne_zero h_pi_x_ne
    have h_div_le_one : (Real.sin (Real.pi * x))^2 / (Real.pi * x)^2 ≤ 1 := by
      exact (div_le_one₀ h_den_pos).mpr h_sin_le_x
    linarith

end InfoGeometry.Canonical.MontgomeryGUE
