import Mathlib
import proofs.SplitOctonionAlgebra
import proofs.SplitOctonionNorm44
import proofs.SplitOctonionTrialityCore
import proofs.SplitOctonionLeftRightMultiplication
import proofs.SplitOctonionAlternativityHelpers
import proofs.SplitOctonionTrialityNormalForm
import proofs.SplitOctonionNucleus

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionTrialityCore
open Quaternion

-- Vector projection of the triality algebra
def π_V : trialityLieSubalgebra →ₗ[ℝ] (SplitOct →ₗ[ℝ] SplitOct) where
  toFun T := T.val.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem triality_inj : LinearMap.ker π_V = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  rw [LinearMap.mem_ker] at hT
  have hA : (T : TrialityAmbient).1.val = 0 := hT
  have ht : IsTriality (T : TrialityAmbient) := T.property
  have hB_skew := (T : TrialityAmbient).2.1.property
  have hC_skew := (T : TrialityAmbient).2.2.property
  
  have hB_val : ∀ x, (T : TrialityAmbient).2.1.val x = - (x * (T : TrialityAmbient).2.2.val 1) := by
    intro x
    have h1 : (T : TrialityAmbient).1.val (x * 1) = (T : TrialityAmbient).2.1.val x * 1 + x * (T : TrialityAmbient).2.2.val 1 := ht x 1
    have hA_eval : (T : TrialityAmbient).1.val (x * 1) = 0 := by rw [hA, LinearMap.zero_apply]
    rw [hA_eval] at h1
    rw [mul_one] at h1
    exact eq_neg_iff_add_eq_zero.mpr h1.symm
  
  have hC_val : ∀ y, (T : TrialityAmbient).2.2.val y = - ((T : TrialityAmbient).2.1.val 1 * y) := by
    intro y
    have h1 : (T : TrialityAmbient).1.val (1 * y) = (T : TrialityAmbient).2.1.val 1 * y + 1 * (T : TrialityAmbient).2.2.val y := ht 1 y
    have hA_eval : (T : TrialityAmbient).1.val (1 * y) = 0 := by rw [hA, LinearMap.zero_apply]
    rw [hA_eval] at h1
    rw [one_mul, add_comm] at h1
    exact eq_neg_iff_add_eq_zero.mpr h1.symm

  let b := (T : TrialityAmbient).2.1.val 1
  have hC1 : (T : TrialityAmbient).2.2.val 1 = - b := by
    have h1 := hC_val 1
    simp only [mul_one] at h1
    exact h1

  have hBx : ∀ x, (T : TrialityAmbient).2.1.val x = x * b := by
    intro x
    have h1 := hB_val x
    rw [hC1, mul_neg, neg_neg] at h1
    exact h1

  have hCy : ∀ y, (T : TrialityAmbient).2.2.val y = - (b * y) := by
    intro y
    exact hC_val y

  have hnuc : ∀ x y, (x * b) * y = x * (b * y) := by
    intro x y
    have h1 : (T : TrialityAmbient).1.val (x * y) = (T : TrialityAmbient).2.1.val x * y + x * (T : TrialityAmbient).2.2.val y := ht x y
    have hA_eval : (T : TrialityAmbient).1.val (x * y) = 0 := by rw [hA, LinearMap.zero_apply]
    rw [hA_eval] at h1
    have h2 : (T : TrialityAmbient).2.1.val x * y + x * (T : TrialityAmbient).2.2.val y = (x * b) * y - x * (b * y) := by
      rw [hBx x, hCy y, mul_neg, sub_eq_add_neg]
    rw [h1.symm] at h2
    exact sub_eq_zero.mp h2.symm

  have h_b_real := middleNucleus_eq_scalar b hnuc

  have hB_skew_1 := hB_skew 1 1
  have hB_skew_2 : splitBilinForm b 1 + splitBilinForm 1 b = 0 := by
    have h3 : splitBilinForm ((T : TrialityAmbient).2.1.val 1) 1 = - splitBilinForm 1 ((T : TrialityAmbient).2.1.val 1) := by
      exact hB_skew_1
    have h4 : (T : TrialityAmbient).2.1.val 1 = b := rfl
    rw [h4] at h3
    exact eq_neg_iff_add_eq_zero.mp h3
  
  have h_b_re : b.a.re = 0 := by
    have h_eval : splitBilinForm b 1 = b.a.re := by
      dsimp [splitBilinForm, splitBilinear, splitNorm, one_def, smul_def, add_def, sub_def, neg_def, Quaternion.normSq]
      ring
    have h_eval2 : splitBilinForm 1 b = b.a.re := by
      dsimp [splitBilinForm, splitBilinear, splitNorm, one_def, smul_def, add_def, sub_def, neg_def, Quaternion.normSq]
      ring
    rw [h_eval, h_eval2] at hB_skew_2
    linarith

  have h_b_zero : b = 0 := by
    rw [h_b_real]
    ext
    · exact h_b_re
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

  have hB_zero : (T : TrialityAmbient).2.1.val = 0 := by
    apply LinearMap.ext
    intro x
    rw [hBx x, h_b_zero, mul_zero, LinearMap.zero_apply]

  have hC_zero : (T : TrialityAmbient).2.2.val = 0 := by
    apply LinearMap.ext
    intro y
    rw [hCy y, h_b_zero, zero_mul, neg_zero, LinearMap.zero_apply]

  have hT_eq_0 : T.val = 0 := by
    have hA_eq : T.val.1 = 0 := ZeroMemClass.coe_eq_zero.mp hA
    have hB_eq : T.val.2.1 = 0 := ZeroMemClass.coe_eq_zero.mp hB_zero
    have hC_eq : T.val.2.2 = 0 := ZeroMemClass.coe_eq_zero.mp hC_zero
    exact Prod.ext hA_eq (Prod.ext hB_eq hC_eq)
  
  exact ZeroMemClass.coe_eq_zero.mp hT_eq_0

-- The inverse coordinate formulas:
set_option linter.unusedSimpArgs false in
lemma triality_inv_coord (T : trialityLieSubalgebra) :
  let α := (1 / 3 : ℝ) • ((2 : ℝ) • (T : TrialityAmbient).2.1.val 1 + (T : TrialityAmbient).2.2.val 1)
  let β := (1 / 3 : ℝ) • ((T : TrialityAmbient).2.1.val 1 + (2 : ℝ) • (T : TrialityAmbient).2.2.val 1)
  (T : TrialityAmbient).2.1.val 1 = (2 : ℝ) • α - β ∧ (T : TrialityAmbient).2.2.val 1 = -α + (2 : ℝ) • β := by
  intro α β
  dsimp [α, β]
  constructor
  · ext1 <;> ext1 <;> {
      simp only [smul_def, add_def, sub_def, neg_def,
                 Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
                 Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
                 Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
                 Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
                 smul_eq_mul]
      ring
    }
  · ext1 <;> ext1 <;> {
      simp only [smul_def, add_def, sub_def, neg_def,
                 Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
                 Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
                 Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
                 Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
                 smul_eq_mul]
      ring
    }

