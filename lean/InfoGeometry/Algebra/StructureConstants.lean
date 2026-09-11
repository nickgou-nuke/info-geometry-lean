/-
Phase 3: Structure Constants f_{abc} and d_{abc} for su(3)
- Computable finite tables for the 8×8×8 structure constants
- Commutator and anticommutator formulas
- Normalization identities
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.SpecialUnitary
import InfoGeometry.Algebra.GellMannBasis

open Matrix
open Fin
open Complex
open LieAlgebra
open InfoGeometry.Algebra.GellMann

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace InfoGeometry.Algebra.StructureConstants

/-- Structure constants f_{abc} as real numbers -/
noncomputable def f : Fin 8 → Fin 8 → Fin 8 → ℝ := fun a b c =>
  if a = 0 ∧ b = 1 ∧ c = 2 then 2
  else if a = 1 ∧ b = 2 ∧ c = 0 then 2
  else if a = 2 ∧ b = 0 ∧ c = 1 then 2
  else if a = 1 ∧ b = 0 ∧ c = 2 then -2
  else if a = 0 ∧ b = 2 ∧ c = 1 then -2
  else if a = 2 ∧ b = 1 ∧ c = 0 then -2
  else if a = 0 ∧ b = 3 ∧ c = 6 then 1
  else if a = 3 ∧ b = 6 ∧ c = 0 then 1
  else if a = 6 ∧ b = 0 ∧ c = 3 then 1
  else if a = 3 ∧ b = 0 ∧ c = 6 then -1
  else if a = 0 ∧ b = 6 ∧ c = 3 then -1
  else if a = 6 ∧ b = 3 ∧ c = 0 then -1
  else if a = 0 ∧ b = 4 ∧ c = 5 then -1
  else if a = 4 ∧ b = 5 ∧ c = 0 then -1
  else if a = 5 ∧ b = 0 ∧ c = 4 then -1
  else if a = 4 ∧ b = 0 ∧ c = 5 then 1
  else if a = 0 ∧ b = 5 ∧ c = 4 then 1
  else if a = 5 ∧ b = 4 ∧ c = 0 then 1
  else if a = 1 ∧ b = 3 ∧ c = 5 then 1
  else if a = 3 ∧ b = 5 ∧ c = 1 then 1
  else if a = 5 ∧ b = 1 ∧ c = 3 then 1
  else if a = 3 ∧ b = 1 ∧ c = 5 then -1
  else if a = 1 ∧ b = 5 ∧ c = 3 then -1
  else if a = 5 ∧ b = 3 ∧ c = 1 then -1
  else if a = 1 ∧ b = 4 ∧ c = 6 then 1
  else if a = 4 ∧ b = 6 ∧ c = 1 then 1
  else if a = 6 ∧ b = 1 ∧ c = 4 then 1
  else if a = 4 ∧ b = 1 ∧ c = 6 then -1
  else if a = 1 ∧ b = 6 ∧ c = 4 then -1
  else if a = 6 ∧ b = 4 ∧ c = 1 then -1
  else if a = 2 ∧ b = 3 ∧ c = 4 then 1
  else if a = 3 ∧ b = 4 ∧ c = 2 then 1
  else if a = 4 ∧ b = 2 ∧ c = 3 then 1
  else if a = 3 ∧ b = 2 ∧ c = 4 then -1
  else if a = 2 ∧ b = 4 ∧ c = 3 then -1
  else if a = 4 ∧ b = 3 ∧ c = 2 then -1
  else if a = 2 ∧ b = 5 ∧ c = 6 then -1
  else if a = 5 ∧ b = 6 ∧ c = 2 then -1
  else if a = 6 ∧ b = 2 ∧ c = 5 then -1
  else if a = 5 ∧ b = 2 ∧ c = 6 then 1
  else if a = 2 ∧ b = 6 ∧ c = 5 then 1
  else if a = 6 ∧ b = 5 ∧ c = 2 then 1
  else if a = 3 ∧ b = 4 ∧ c = 7 then Real.sqrt 3
  else if a = 4 ∧ b = 7 ∧ c = 3 then Real.sqrt 3
  else if a = 7 ∧ b = 3 ∧ c = 4 then Real.sqrt 3
  else if a = 4 ∧ b = 3 ∧ c = 7 then -Real.sqrt 3
  else if a = 3 ∧ b = 7 ∧ c = 4 then -Real.sqrt 3
  else if a = 7 ∧ b = 4 ∧ c = 3 then -Real.sqrt 3
  else if a = 5 ∧ b = 6 ∧ c = 7 then Real.sqrt 3
  else if a = 6 ∧ b = 7 ∧ c = 5 then Real.sqrt 3
  else if a = 7 ∧ b = 5 ∧ c = 6 then Real.sqrt 3
  else if a = 6 ∧ b = 5 ∧ c = 7 then -Real.sqrt 3
  else if a = 5 ∧ b = 7 ∧ c = 6 then -Real.sqrt 3
  else if a = 7 ∧ b = 6 ∧ c = 5 then -Real.sqrt 3
  else 0

/-- Symmetric coefficients d_{abc} as real numbers -/
noncomputable def d : Fin 8 → Fin 8 → Fin 8 → ℝ := fun a b c =>
  if a = 0 ∧ b = 0 ∧ c = 7 then 2 / Real.sqrt 3
  else if a = 0 ∧ b = 3 ∧ c = 5 then 1
  else if a = 0 ∧ b = 4 ∧ c = 6 then 1
  else if a = 0 ∧ b = 5 ∧ c = 3 then 1
  else if a = 0 ∧ b = 6 ∧ c = 4 then 1
  else if a = 0 ∧ b = 7 ∧ c = 0 then 2 / Real.sqrt 3
  else if a = 1 ∧ b = 1 ∧ c = 7 then 2 / Real.sqrt 3
  else if a = 1 ∧ b = 3 ∧ c = 6 then -1
  else if a = 1 ∧ b = 4 ∧ c = 5 then 1
  else if a = 1 ∧ b = 5 ∧ c = 4 then 1
  else if a = 1 ∧ b = 6 ∧ c = 3 then -1
  else if a = 1 ∧ b = 7 ∧ c = 1 then 2 / Real.sqrt 3
  else if a = 2 ∧ b = 2 ∧ c = 7 then 2 / Real.sqrt 3
  else if a = 2 ∧ b = 3 ∧ c = 3 then 1
  else if a = 2 ∧ b = 4 ∧ c = 4 then 1
  else if a = 2 ∧ b = 5 ∧ c = 5 then -1
  else if a = 2 ∧ b = 6 ∧ c = 6 then -1
  else if a = 2 ∧ b = 7 ∧ c = 2 then 2 / Real.sqrt 3
  else if a = 3 ∧ b = 0 ∧ c = 5 then 1
  else if a = 3 ∧ b = 1 ∧ c = 6 then -1
  else if a = 3 ∧ b = 2 ∧ c = 3 then 1
  else if a = 3 ∧ b = 3 ∧ c = 2 then 1
  else if a = 3 ∧ b = 3 ∧ c = 7 then -1 / Real.sqrt 3
  else if a = 3 ∧ b = 5 ∧ c = 0 then 1
  else if a = 3 ∧ b = 6 ∧ c = 1 then -1
  else if a = 3 ∧ b = 7 ∧ c = 3 then -1 / Real.sqrt 3
  else if a = 4 ∧ b = 0 ∧ c = 6 then 1
  else if a = 4 ∧ b = 1 ∧ c = 5 then 1
  else if a = 4 ∧ b = 2 ∧ c = 4 then 1
  else if a = 4 ∧ b = 4 ∧ c = 2 then 1
  else if a = 4 ∧ b = 4 ∧ c = 7 then -1 / Real.sqrt 3
  else if a = 4 ∧ b = 5 ∧ c = 1 then 1
  else if a = 4 ∧ b = 6 ∧ c = 0 then 1
  else if a = 4 ∧ b = 7 ∧ c = 4 then -1 / Real.sqrt 3
  else if a = 5 ∧ b = 0 ∧ c = 3 then 1
  else if a = 5 ∧ b = 1 ∧ c = 4 then 1
  else if a = 5 ∧ b = 2 ∧ c = 5 then -1
  else if a = 5 ∧ b = 3 ∧ c = 0 then 1
  else if a = 5 ∧ b = 4 ∧ c = 1 then 1
  else if a = 5 ∧ b = 5 ∧ c = 2 then -1
  else if a = 5 ∧ b = 5 ∧ c = 7 then -1 / Real.sqrt 3
  else if a = 5 ∧ b = 7 ∧ c = 5 then -1 / Real.sqrt 3
  else if a = 6 ∧ b = 0 ∧ c = 4 then 1
  else if a = 6 ∧ b = 1 ∧ c = 3 then -1
  else if a = 6 ∧ b = 2 ∧ c = 6 then -1
  else if a = 6 ∧ b = 3 ∧ c = 1 then -1
  else if a = 6 ∧ b = 4 ∧ c = 0 then 1
  else if a = 6 ∧ b = 6 ∧ c = 2 then -1
  else if a = 6 ∧ b = 6 ∧ c = 7 then -1 / Real.sqrt 3
  else if a = 6 ∧ b = 7 ∧ c = 6 then -1 / Real.sqrt 3
  else if a = 7 ∧ b = 0 ∧ c = 0 then 2 / Real.sqrt 3
  else if a = 7 ∧ b = 1 ∧ c = 1 then 2 / Real.sqrt 3
  else if a = 7 ∧ b = 2 ∧ c = 2 then 2 / Real.sqrt 3
  else if a = 7 ∧ b = 3 ∧ c = 3 then -1 / Real.sqrt 3
  else if a = 7 ∧ b = 4 ∧ c = 4 then -1 / Real.sqrt 3
  else if a = 7 ∧ b = 5 ∧ c = 5 then -1 / Real.sqrt 3
  else if a = 7 ∧ b = 6 ∧ c = 6 then -1 / Real.sqrt 3
  else if a = 7 ∧ b = 7 ∧ c = 7 then -2 / Real.sqrt 3
  else 0

theorem commutator_formula (a b : Fin 8) :
    ⁅gellMann a, gellMann b⁆ = ∑ c : Fin 8, (f a b c : ℝ) • gellMann c := by
  have h_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h_ne : (Real.sqrt 3 : ℂ) ≠ 0 := by
    intro h
    have h_real : Real.sqrt 3 = 0 := by exact_mod_cast h
    have h_sq_zero : Real.sqrt 3 * Real.sqrt 3 = 0 := by rw [h_real, mul_zero]
    rw [h_sq] at h_sq_zero
    norm_num at h_sq_zero
  have h_cdiv1 : (I * (Real.sqrt 3 : ℂ)⁻¹) * (I * (Real.sqrt 3 : ℂ)⁻¹) = -1 / 3 := by
    have : (I * (Real.sqrt 3 : ℂ)⁻¹) * (I * (Real.sqrt 3 : ℂ)⁻¹) = (I * I) * ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ))⁻¹ := by
      rw [mul_inv]
      ring
    rw [this, ← Complex.ofReal_mul, h_sq, I_mul_I]
    norm_num
  have h_cdiv2 : (I * (Real.sqrt 3 : ℂ)⁻¹) * (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) = 2 / 3 := by
    have : (I * (Real.sqrt 3 : ℂ)⁻¹) * (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) = (I * -(2 * I)) * ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ))⁻¹ := by
      rw [mul_inv]
      ring
    rw [this, ← Complex.ofReal_mul, h_sq]
    have h_I2 : I * -(2 * I) = 2 := by
      have : I * -(2 * I) = -2 * (I * I) := by ring
      rw [this, I_mul_I]
      ring
    rw [h_I2]
    norm_num
  have h_cdiv3 : (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) * (I * (Real.sqrt 3 : ℂ)⁻¹) = 2 / 3 := by
    rw [mul_comm]
    exact h_cdiv2
  have h_cdiv4 : (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) * (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) = -4 / 3 := by
    have : (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) * (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) = (-(2 * I) * -(2 * I)) * ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ))⁻¹ := by
      rw [mul_inv]
      ring
    rw [this, ← Complex.ofReal_mul, h_sq]
    have h_I2 : -(2 * I) * -(2 * I) = -4 := by
      have : -(2 * I) * -(2 * I) = 4 * (I * I) := by ring
      rw [this, I_mul_I]
      ring
    rw [h_I2]
    norm_num
  have h_cmul1 : (Real.sqrt 3 : ℂ) * (I * (Real.sqrt 3 : ℂ)⁻¹) = I := by
    rw [mul_left_comm, mul_inv_cancel₀ h_ne, mul_one]
  have h_cmul2 : (Real.sqrt 3 : ℂ) * (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) = -(2 * I) := by
    rw [mul_left_comm, mul_inv_cancel₀ h_ne, mul_one]
  have h_cmul3 : (I * (Real.sqrt 3 : ℂ)⁻¹) * (Real.sqrt 3 : ℂ) = I := by
    rw [mul_assoc, inv_mul_cancel₀ h_ne, mul_one]
  have h_cmul4 : (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) * (Real.sqrt 3 : ℂ) = -(2 * I) := by
    rw [mul_assoc, inv_mul_cancel₀ h_ne, mul_one]
  have h_cmul5 : -(Real.sqrt 3 : ℂ) * (I * (Real.sqrt 3 : ℂ)⁻¹) = -I := by
    rw [neg_mul, h_cmul1]
  have h_cmul6 : -(Real.sqrt 3 : ℂ) * (-(2 * I) * (Real.sqrt 3 : ℂ)⁻¹) = 2 * I := by
    rw [neg_mul, h_cmul2, neg_neg]
  have h_rsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h_rne : Real.sqrt 3 ≠ 0 := by
    intro h
    have h_sq_zero : Real.sqrt 3 * Real.sqrt 3 = 0 := by rw [h, mul_zero]
    rw [h_rsq] at h_sq_zero
    norm_num at h_sq_zero
  have h_rinv : (Real.sqrt 3)⁻¹ * 3 = Real.sqrt 3 := by
    nth_rw 2 [← h_rsq]
    rw [← mul_assoc, inv_mul_cancel₀ h_rne, one_mul]
  have h_rinv2 : 3 * (Real.sqrt 3)⁻¹ = Real.sqrt 3 := by rw [mul_comm, h_rinv]
  have h_cinv_a : (Real.sqrt 3 : ℂ)⁻¹ * 3 = Real.sqrt 3 := by
    have h_csq : (3 : ℂ) = (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) := by
      rw [← Complex.ofReal_mul, h_sq]
      rfl
    rw [h_csq, ← mul_assoc, inv_mul_cancel₀ h_ne, one_mul]
  have h_cinv_a' : ((Real.sqrt 3)⁻¹ : ℂ) * 3 = Real.sqrt 3 := h_cinv_a
  have h_cinv_b : (Real.sqrt 3 : ℂ)⁻¹ * ((3 : ℝ) : ℂ) = Real.sqrt 3 := by
    have h_csq : ((3 : ℝ) : ℂ) = (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) := by
      rw [← Complex.ofReal_mul, h_sq]
    rw [h_csq, ← mul_assoc, inv_mul_cancel₀ h_ne, one_mul]
  have h_cinv_b' : ((Real.sqrt 3)⁻¹ : ℂ) * ((3 : ℝ) : ℂ) = Real.sqrt 3 := h_cinv_b
  have h_cinv_c : (Real.sqrt 3 : ℂ)⁻¹ * ((3 : ℕ) : ℂ) = Real.sqrt 3 := by
    have : ((3 : ℕ) : ℂ) = ((3 : ℝ) : ℂ) := by norm_cast
    rw [this, h_cinv_b]
  have h_cinv_c' : ((Real.sqrt 3)⁻¹ : ℂ) * ((3 : ℕ) : ℂ) = Real.sqrt 3 := h_cinv_c
  have h_cinv_d : (Real.sqrt 3 : ℂ)⁻¹ * ((3 : ℤ) : ℂ) = Real.sqrt 3 := by
    have : ((3 : ℤ) : ℂ) = ((3 : ℝ) : ℂ) := by norm_cast
    rw [this, h_cinv_b]
  have h_cinv_d' : ((Real.sqrt 3)⁻¹ : ℂ) * ((3 : ℤ) : ℂ) = Real.sqrt 3 := h_cinv_d

  have h_cinv2_a : 3 * (Real.sqrt 3 : ℂ)⁻¹ = Real.sqrt 3 := by rw [mul_comm, h_cinv_a]
  have h_cinv2_a' : 3 * ((Real.sqrt 3)⁻¹ : ℂ) = Real.sqrt 3 := by rw [mul_comm, h_cinv_a']
  have h_cinv2_b : ((3 : ℝ) : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ = Real.sqrt 3 := by rw [mul_comm, h_cinv_b]
  have h_cinv2_b' : ((3 : ℝ) : ℂ) * ((Real.sqrt 3)⁻¹ : ℂ) = Real.sqrt 3 := by rw [mul_comm, h_cinv_b']
  have h_cinv2_c : ((3 : ℕ) : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ = Real.sqrt 3 := by rw [mul_comm, h_cinv_c]
  have h_cinv2_c' : ((3 : ℕ) : ℂ) * ((Real.sqrt 3)⁻¹ : ℂ) = Real.sqrt 3 := by rw [mul_comm, h_cinv_c']
  have h_cinv2_d : ((3 : ℤ) : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ = Real.sqrt 3 := by rw [mul_comm, h_cinv_d]
  have h_cinv2_d' : ((3 : ℤ) : ℂ) * ((Real.sqrt 3)⁻¹ : ℂ) = Real.sqrt 3 := by rw [mul_comm, h_cinv_d']

  fin_cases a <;> fin_cases b <;> {
    apply Subtype.ext
    simp [gellMann, gellMannArray, gellMann1, gellMann2, gellMann3, gellMann4, gellMann5, gellMann6, gellMann7, gellMann8, f, LieRing.of_associative_ring_bracket, Fin.sum_univ_eight, h_cdiv1, h_cdiv2, h_cdiv3, h_cdiv4, h_cmul1, h_cmul2, h_cmul3, h_cmul4, h_cmul5, h_cmul6]
    repeat constructor
    all_goals {
      try rfl
      try apply Subtype.ext
      try { funext i j <;> fin_cases i <;> fin_cases j <;> { try ring_nf; try rfl } }
      try { funext i <;> fin_cases i <;> { try ring_nf; try rfl } }
      try repeat constructor
      all_goals {
        try rfl
        try apply Subtype.ext
        try { funext i j <;> fin_cases i <;> fin_cases j <;> { try ring_nf; try rfl } }
        try { funext i <;> fin_cases i <;> { try ring_nf; try rfl } }
        try ring_nf
        try repeat rw [mul_assoc]
        try rw [h_cinv_a]
        try rw [h_cinv_a']
        try rw [h_cinv_b]
        try rw [h_cinv_b']
        try rw [h_cinv_c]
        try rw [h_cinv_c']
        try rw [h_cinv_d]
        try rw [h_cinv_d']
        try rw [h_cinv2_a]
        try rw [h_cinv2_a']
        try rw [h_cinv2_b]
        try rw [h_cinv2_b']
        try rw [h_cinv2_c]
        try rw [h_cinv2_c']
        try rw [h_cinv2_d]
        try rw [h_cinv2_d']
        try simp only [h_rinv, h_rinv2, h_cinv_a, h_cinv_a', h_cinv_b, h_cinv_b', h_cinv_c, h_cinv_c', h_cinv_d, h_cinv_d', h_cinv2_a, h_cinv2_a', h_cinv2_b, h_cinv2_b', h_cinv2_c, h_cinv2_c', h_cinv2_d, h_cinv2_d']
        try simp [h_cdiv1, h_cdiv2, h_cdiv3, h_cdiv4, h_cmul1, h_cmul2, h_cmul3, h_cmul4, h_cmul5, h_cmul6]
        try repeat rw [← mul_assoc]
        try simp [h_cdiv1, h_cdiv2, h_cdiv3, h_cdiv4, h_cmul1, h_cmul2, h_cmul3, h_cmul4, h_cmul5, h_cmul6]
        try ring_nf
        try rfl
        try { funext i j <;> fin_cases i <;> fin_cases j <;> { try ring_nf; try rfl } }
        try { funext i <;> fin_cases i <;> { try ring_nf; try rfl } }
      }
    }
  }

/-- f antisymmetry: f_{abc} = -f_{bac} -/
theorem f_antisym_ab (a b c : Fin 8) : f a b c = -f b a c := by
  fin_cases a
  all_goals fin_cases b
  all_goals fin_cases c
  all_goals simp [f]

theorem f_antisym_bc (a b c : Fin 8) : f a b c = -f a c b := by
  fin_cases a
  all_goals fin_cases b
  all_goals fin_cases c
  all_goals simp [f]

/-- f cyclic invariance (even permutation invariance): f_{abc} = f_{bca} -/
theorem f_cyclic (a b c : Fin 8) : f a b c = f b c a := by
  fin_cases a
  all_goals fin_cases b
  all_goals fin_cases c
  all_goals rfl

/-- d symmetry: d_{abc} = d_{bac} = d_{bca} -/
theorem d_sym_ab (a b c : Fin 8) : d a b c = d b a c := by
  fin_cases a
  all_goals fin_cases b
  all_goals fin_cases c
  all_goals rfl

theorem d_sym_bc (a b c : Fin 8) : d a b c = d b c a := by
  fin_cases a
  all_goals fin_cases b
  all_goals fin_cases c
  all_goals rfl

/-- Normalization: ∑_{c,e} d_{ace} d_{bce} = (20/3) δ_{ab} -/
theorem d_normalization (a b : Fin 8) :
    (∑ c : Fin 8, ∑ e : Fin 8, d a c e * d b c e) = (20 / 3 : ℝ) * (if a = b then 1 else 0 : ℝ) := by
  have h_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h_div1 : (2 / Real.sqrt 3) * (2 / Real.sqrt 3) = (4 / 3 : ℝ) := by
    rw [div_mul_div_comm, h_sq]
    norm_num
  have h_div2 : (-1 / Real.sqrt 3) * (-1 / Real.sqrt 3) = (1 / 3 : ℝ) := by
    rw [div_mul_div_comm]
    have : (-1 : ℝ) * -1 = 1 := by ring
    rw [this, h_sq]
  have h_div3 : (1 / Real.sqrt 3) * (1 / Real.sqrt 3) = (1 / 3 : ℝ) := by
    rw [div_mul_div_comm, h_sq]
    norm_num
  have h_div4 : (-2 / Real.sqrt 3) * (-2 / Real.sqrt 3) = (4 / 3 : ℝ) := by
    rw [div_mul_div_comm]
    have : (-2 : ℝ) * -2 = 4 := by ring
    rw [this, h_sq]
  fin_cases a
  all_goals fin_cases b
  all_goals { simp [d, Fin.sum_univ_eight, h_sq, h_div1, h_div2, h_div3, h_div4]; try ring }



/-- From [λₐ, λ_b] = 2i f_abc λ_c, antisymmetry of commutator -/
theorem f_antisym_omega : ∀ (a b c : Fin 8), f a b c = -f b a c := by exact f_antisym_ab


/-- From Jacobi identity [λₐ, [λ_b, λ_c]] + cyclic = 0 -/
theorem f_cyclic_omega : ∀ (a b c : Fin 8), f a b c = f b c a := by exact f_cyclic


/-- From {λₐ, λ_b} = (4/3)δₐᵦ + 2d_abc λ_c, symmetry of anticommutator -/
theorem d_sym_omega : ∀ (a b c : Fin 8), d a b c = d b a c := by exact d_sym_ab

end InfoGeometry.Algebra.StructureConstants
