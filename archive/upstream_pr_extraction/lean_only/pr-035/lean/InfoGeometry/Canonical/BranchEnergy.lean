import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.MixedVarianceDeviance
import Mathlib.Tactic

namespace InfoGeometry.Canonical

open Real

noncomputable def positiveBranchEnergy (a b : ℝ) (ha : a ≠ 0) (X μ : ℝ) : ℝ :=
  if μ ≤ X then D_affine a b X μ else 0

noncomputable def negativeBranchEnergy (a b : ℝ) (ha : a ≠ 0) (X μ : ℝ) : ℝ :=
  if X < μ then D_affine a b X μ else 0

theorem branchEnergy_add (a b : ℝ) (ha : a ≠ 0) (X μ : ℝ) :
    positiveBranchEnergy a b ha X μ + negativeBranchEnergy a b ha X μ = D_affine a b X μ := by
  by_cases h : μ ≤ X
  · have hnlt : ¬ X < μ := not_lt_of_ge h
    simp [positiveBranchEnergy, negativeBranchEnergy, h, hnlt]
  · have hlt : X < μ := lt_of_not_ge h
    simp [positiveBranchEnergy, negativeBranchEnergy, h, hlt]

theorem branchEnergy_mul_eq_zero (a b : ℝ) (ha : a ≠ 0) (X μ : ℝ) :
    positiveBranchEnergy a b ha X μ * negativeBranchEnergy a b ha X μ = 0 := by
  by_cases h : μ ≤ X
  · have hnlt : ¬ X < μ := not_lt_of_ge h
    simp [positiveBranchEnergy, negativeBranchEnergy, h, hnlt]
  · have hlt : X < μ := lt_of_not_ge h
    simp [positiveBranchEnergy, negativeBranchEnergy, h, hlt]

noncomputable def signedRootDeviance (a b : ℝ) (ha : a ≠ 0) (X μ : ℝ) : ℝ :=
  if μ ≤ X then
    Real.sqrt (D_affine a b X μ)
  else
    -Real.sqrt (D_affine a b X μ)

noncomputable def signedRootPos (a b : ℝ) (ha : a ≠ 0) (X μ : ℝ) : ℝ :=
  max (signedRootDeviance a b ha X μ) 0

noncomputable def signedRootNeg (a b : ℝ) (ha : a ≠ 0) (X μ : ℝ) : ℝ :=
  max (-signedRootDeviance a b ha X μ) 0

lemma deviance_core_nonneg (y : ℝ) (hy : 0 < y) :
    0 ≤ y - 1 - log y := by
  have H : log y ≤ y - 1 := log_le_sub_one_of_pos hy
  linarith

lemma deviance_core_eq_zero_iff (y : ℝ) (hy : 0 < y) :
    y - 1 - log y = 0 ↔ y = 1 := by
  constructor
  · intro h
    by_contra hne
    have h_lt : log y < y - 1 := log_lt_sub_one_of_pos hy hne
    linarith
  · intro h
    rw [h, log_one]
    norm_num

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

lemma x_log_div_sub_eq_zero_iff (x μ : ℝ) (hx : 0 < x) (hμ : 0 < μ) :
    x * log (x / μ) - (x - μ) = 0 ↔ x = μ := by
  have h_eq : x * log (x / μ) - (x - μ) = x * (log (x / μ) - (1 - μ / x)) := by
    have h1 : x * (1 - μ / x) = x - μ := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hx.ne']
    rw [mul_sub, h1]
  rw [h_eq]
  have hx_pos : x ≠ 0 := hx.ne'
  rw [mul_eq_zero, sub_eq_zero]
  simp only [hx_pos, false_or]
  have h_log : log (x / μ) = - log (μ / x) := by
    rw [log_div hx.ne' hμ.ne', log_div hμ.ne' hx.ne']
    ring
  rw [h_log]
  have h1 : - log (μ / x) = 1 - μ / x ↔ μ / x - 1 - log (μ / x) = 0 := by
    constructor
    · intro h; linarith
    · intro h; linarith
  rw [h1]
  rw [deviance_core_eq_zero_iff (μ / x) (div_pos hμ hx)]
  have h_div : μ / x = 1 ↔ μ = x := div_eq_one_iff_eq hx.ne'
  rw [h_div]
  exact eq_comm

theorem affineDeviance_nonneg (a b x μ : ℝ) (ha : a ≠ 0) (hx : 0 < a * x + b) (hμ : 0 < a * μ + b) :
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

theorem affineDeviance_eq_zero_iff (a b x μ : ℝ) (ha : a ≠ 0) (hx : 0 < a * x + b) (hμ : 0 < a * μ + b) :
    D_affine a b x μ = 0 ↔ x = μ := by
  dsimp [D_affine]
  have h_pos : 2 / a ^ 2 ≠ 0 := div_ne_zero (by norm_num) (pow_ne_zero 2 ha)
  rw [mul_eq_zero]
  simp only [h_pos, false_or]
  have h_eq : (a * x + b) * log ((a * x + b) / (a * μ + b)) - a * (x - μ) = 
              (a * x + b) * log ((a * x + b) / (a * μ + b)) - ((a * x + b) - (a * μ + b)) := by
    congr 1
    ring
  rw [h_eq]
  rw [x_log_div_sub_eq_zero_iff (a * x + b) (a * μ + b) hx hμ]
  constructor
  · intro h
    have h1 : a * x = a * μ := by linarith
    exact (mul_right_inj' ha).mp h1
  · intro h
    rw [h]

theorem signedRoot_pos_sq (a b : ℝ) (ha : a ≠ 0) (X μ : ℝ) (hx : 0 < a * X + b) (hμ : 0 < a * μ + b) :
    signedRootPos a b ha X μ ^ 2 = positiveBranchEnergy a b ha X μ := by
  have hD : 0 ≤ D_affine a b X μ := affineDeviance_nonneg a b X μ ha hx hμ
  by_cases h : μ ≤ X
  · simp [signedRootPos, signedRootDeviance, positiveBranchEnergy, h, Real.sqrt_nonneg, Real.sq_sqrt hD]
  · have hlt : X < μ := lt_of_not_ge h
    simp [signedRootPos, signedRootDeviance, positiveBranchEnergy, h, Real.sqrt_nonneg]

theorem signedRoot_neg_sq (a b : ℝ) (ha : a ≠ 0) (X μ : ℝ) (hx : 0 < a * X + b) (hμ : 0 < a * μ + b) :
    signedRootNeg a b ha X μ ^ 2 = negativeBranchEnergy a b ha X μ := by
  have hD : 0 ≤ D_affine a b X μ := affineDeviance_nonneg a b X μ ha hx hμ
  by_cases h : μ ≤ X
  · simp [signedRootNeg, signedRootDeviance, negativeBranchEnergy, h, Real.sqrt_nonneg]
  · have hlt : X < μ := lt_of_not_ge h
    simp [signedRootNeg, signedRootDeviance, negativeBranchEnergy, h, Real.sqrt_nonneg, Real.sq_sqrt hD]

end InfoGeometry.Canonical
