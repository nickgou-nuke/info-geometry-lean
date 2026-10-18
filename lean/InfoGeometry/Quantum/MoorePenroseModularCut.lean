/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Moore–Penrose Modular Cut: Taming the Singular Density Matrix
Target: `InfoGeometry/Quantum/MoorePenroseModularCut.lean`

Formalizes:
1. Moore–Penrose pseudoinverse ρ⁺ for diagonal density matrices with zero modes.
2. The 4 Penrose identities:
   - ρ ρ⁺ ρ = ρ
   - ρ⁺ ρ ρ⁺ = ρ⁺
   - (ρ ρ⁺)ᵀ = ρ ρ⁺ = P_supp
   - (ρ⁺ ρ)ᵀ = ρ⁺ ρ = P_supp
3. P_supp is an idempotent orthogonal projector: P² = P.
4. Annihilation of the evicted/masked kernel: ρ⁺ (1 - P) = 0.
5. The regularized KMS commutation on the active context support.
-/

noncomputable section

namespace QuantumContext.MoorePenrose

open Finset

variable {n : ℕ}

/-! ### 1. The Moore–Penrose Pseudoinverse Definition -/

/-- The Moore–Penrose pseudoinverse of a diagonal density vector:
    Sends zero eigenvalues strictly to 0, avoiding 1/0 singularity. -/
def moorePenrose (ρ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if ρ i = 0 then 0 else (ρ i)⁻¹

/-- The Support Projector P = ρ · ρ⁺. -/
def supportProj (ρ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if ρ i = 0 then 0 else 1

/-! ### 2. Proof of the Moore–Penrose Identities -/

/-- Penrose Identity 1: ρ · ρ⁺ · ρ = ρ. -/
theorem penrose_one (ρ : Fin n → ℝ) :
    (fun i => ρ i * moorePenrose ρ i * ρ i) = ρ := by
  ext i
  dsimp [moorePenrose]
  split_ifs with h
  · rw [h, zero_mul, zero_mul]
  · rw [mul_inv_cancel₀ h, one_mul]

/-- Penrose Identity 2: ρ⁺ · ρ · ρ⁺ = ρ⁺. -/
theorem penrose_two (ρ : Fin n → ℝ) :
    (fun i => moorePenrose ρ i * ρ i * moorePenrose ρ i) = moorePenrose ρ := by
  ext i
  dsimp [moorePenrose]
  split_ifs with h
  · ring
  · rw [inv_mul_cancel₀ h, one_mul]

/-- Identification of ρ · ρ⁺ with the Support Projector. -/
theorem mul_pinv_eq_support (ρ : Fin n → ℝ) :
    (fun i => ρ i * moorePenrose ρ i) = supportProj ρ := by
  ext i
  dsimp [moorePenrose, supportProj]
  split_ifs with h
  · rw [h, zero_mul]
  · exact mul_inv_cancel₀ h

/-- Identification of ρ⁺ · ρ with the Support Projector. -/
theorem pinv_mul_eq_support (ρ : Fin n → ℝ) :
    (fun i => moorePenrose ρ i * ρ i) = supportProj ρ := by
  ext i
  dsimp [moorePenrose, supportProj]
  split_ifs with h
  · rw [zero_mul]
  · exact inv_mul_cancel₀ h

/-! ### 3. Idempotency and Kernel Annihilation -/

/-- P_supp is an idempotent orthogonal projector: P² = P. -/
theorem support_idempotent (ρ : Fin n → ℝ) :
    (fun i => supportProj ρ i * supportProj ρ i) = supportProj ρ := by
  ext i
  by_cases h : ρ i = 0
  · simp [supportProj, h]
    <;> ring
  · simp [supportProj, h]
    <;> ring

/-- The Eviction/Mask Projector Q = 1 - P. -/
def evictionProj (ρ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 1 - supportProj ρ i

/-- Annihilation of the evicted kernel: ρ⁺ · Q = 0. -/
theorem pinv_annihilates_eviction (ρ : Fin n → ℝ) :
    (fun i => moorePenrose ρ i * evictionProj ρ i) = (fun _ => 0) := by
  ext i
  dsimp [moorePenrose, evictionProj, supportProj]
  split_ifs <;> ring

/-! ### 4. The Regularized KMS Commutation on the Active Context -/

/-- 
On the active support (where supportProj ρ i = 1), 
the Moore–Penrose modular operator satisfies the exact KMS closure:
ρ · A · (ρ · B · ρ⁺) = ρ · B · A.
-/
theorem regularized_kms_on_support (ρ : Fin n → ℝ) (i : Fin n)
    (h_active : supportProj ρ i = 1) (A B : ℝ) :
    ρ i * A * (ρ i * B * moorePenrose ρ i) = ρ i * B * A := by
  dsimp [supportProj] at h_active
  split_ifs at h_active with h_zero
  · revert h_active; norm_num
  · dsimp [moorePenrose]
    simp only [h_zero, ↓reduceIte]
    calc
      ρ i * A * (ρ i * B * (ρ i)⁻¹)
        = (ρ i * A) * (B * (ρ i * (ρ i)⁻¹)) := by ring
      _ = (ρ i * A) * (B * 1) := by rw [mul_inv_cancel₀ h_zero]
      _ = ρ i * B * A := by ring

end QuantumContext.MoorePenrose
