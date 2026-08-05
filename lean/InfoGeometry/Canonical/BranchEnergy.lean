import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.MixedVarianceDeviance
import Mathlib.Tactic

namespace InfoGeometry.Canonical

open Real

/-- The positive branch energy D_+ -/
noncomputable def positiveBranchEnergy (D : ℝ) (X μ : ℝ) : ℝ :=
  if X ≥ μ then D else 0

/-- The negative branch energy D_- -/
noncomputable def negativeBranchEnergy (D : ℝ) (X μ : ℝ) : ℝ :=
  if X < μ then D else 0

theorem branchEnergy_add (D X μ : ℝ) :
    positiveBranchEnergy D X μ + negativeBranchEnergy D X μ = D := by
  dsimp [positiveBranchEnergy, negativeBranchEnergy]
  by_cases h : X ≥ μ
  · rw [if_pos h]
    have h_not : ¬(X < μ) := by linarith
    rw [if_neg h_not]
    ring
  · rw [if_neg h]
    have h_lt : X < μ := by linarith
    rw [if_pos h_lt]
    ring

theorem branchEnergy_mul_eq_zero (D X μ : ℝ) :
    positiveBranchEnergy D X μ * negativeBranchEnergy D X μ = 0 := by
  dsimp [positiveBranchEnergy, negativeBranchEnergy]
  by_cases h : X ≥ μ
  · rw [if_pos h]
    have h_not : ¬(X < μ) := by linarith
    rw [if_neg h_not]
    ring
  · rw [if_neg h]
    have h_lt : X < μ := by linarith
    rw [if_pos h_lt]
    ring

/-- The signed root deviance s(X, μ) -/
noncomputable def signedRoot (D X μ : ℝ) : ℝ :=
  if X ≥ μ then sqrt D else - sqrt D

noncomputable def s_plus (D X μ : ℝ) : ℝ := max (signedRoot D X μ) 0
noncomputable def s_minus (D X μ : ℝ) : ℝ := max (- signedRoot D X μ) 0

theorem signedRoot_pos_sq (D X μ : ℝ) (hD : 0 ≤ D) :
    (s_plus D X μ) ^ 2 = positiveBranchEnergy D X μ := by
  dsimp [s_plus, signedRoot, positiveBranchEnergy]
  by_cases h : X ≥ μ
  · rw [if_pos h, if_pos h]
    have h_sqrt : 0 ≤ sqrt D := sqrt_nonneg D
    rw [max_eq_left h_sqrt, sq_sqrt hD]
  · rw [if_neg h, if_neg h]
    have h_sqrt : - sqrt D ≤ 0 := neg_nonpos.mpr (sqrt_nonneg D)
    rw [max_eq_right h_sqrt, zero_pow (by decide)]

theorem signedRoot_neg_sq (D X μ : ℝ) (hD : 0 ≤ D) :
    (s_minus D X μ) ^ 2 = negativeBranchEnergy D X μ := by
  dsimp [s_minus, signedRoot, negativeBranchEnergy]
  by_cases h : X ≥ μ
  · rw [if_pos h]
    have h_not : ¬(X < μ) := by linarith
    rw [if_neg h_not]
    have h_sqrt : - sqrt D ≤ 0 := neg_nonpos.mpr (sqrt_nonneg D)
    rw [max_eq_right h_sqrt, zero_pow (by decide)]
  · rw [if_neg h]
    have h_lt : X < μ := by linarith
    rw [if_pos h_lt]
    have h_sqrt : 0 ≤ sqrt D := sqrt_nonneg D
    rw [neg_neg, max_eq_left h_sqrt, sq_sqrt hD]

/-- Base lemma for deviance nonnegativity: y - 1 - log y ≥ 0 for y > 0. -/
lemma deviance_core_nonneg (y : ℝ) (hy : 0 < y) :
    0 ≤ y - 1 - log y := by
  have H : log y ≤ y - 1 := log_le_sub_one_of_pos hy
  linarith

/-- Base lemma: x log (x / μ) - (x - μ) ≥ 0 for x, μ > 0. -/
lemma x_log_div_sub_nonneg (x μ : ℝ) (hx : 0 < x) (hμ : 0 < μ) :
    0 ≤ x * log (x / μ) - (x - μ) := by
  have hy := deviance_core_nonneg (μ / x) (div_pos hμ hx)
  have h_log : log (μ / x) = - log (x / μ) := by
    rw [log_div hμ.ne' hx.ne', log_div hx.ne' hμ.ne']
    ring
  rw [h_log] at hy
  have h_plus : 0 ≤ μ / x - 1 + log (x / μ) := by
    have h1 : μ / x - 1 - - log (x / μ) = μ / x - 1 + log (x / μ) := by ring
    rw [← h1]
    exact hy
  have hy_mul : 0 ≤ x * (μ / x - 1 + log (x / μ)) := mul_nonneg hx.le h_plus
  have h_eq : x * (μ / x - 1 + log (x / μ)) = x * log (x / μ) - (x - μ) := by
    rw [mul_add, mul_sub, mul_one, mul_div_cancel₀ _ hx.ne']
    ring
  rwa [← h_eq]

/-- Non-negativity of the affine deviance. -/
theorem affineDeviance_nonneg (a b x μ : ℝ) (hx : 0 < a * x + b) (hμ : 0 < a * μ + b) :
    0 ≤ D_affine a b x μ := by
  dsimp [D_affine]
  have H := x_log_div_sub_nonneg (a * x + b) (a * μ + b) hx hμ
  have h_pos : 0 ≤ 2 / a ^ 2 := div_nonneg (by norm_num) (sq_nonneg a)
  have h_eq : (a * x + b) * log ((a * x + b) / (a * μ + b)) - a * (x - μ) = 
              (a * x + b) * log ((a * x + b) / (a * μ + b)) - ((a * x + b) - (a * μ + b)) := by
    congr 1
    ring
  rw [h_eq]
  exact mul_nonneg h_pos H


end InfoGeometry.Canonical
