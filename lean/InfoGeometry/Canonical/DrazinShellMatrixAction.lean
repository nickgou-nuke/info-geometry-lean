/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.DrazinObliqueShellResolution
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Explicit row/column actions and a nontrivial oblique example -/

noncomputable section

namespace InfoGeometry.Canonical.DrazinShellMatrixAction

open Matrix
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinObliqueShellResolution
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MoorePenrosePowerShells
open InfoGeometry.Singular.MoorePenroseShellDynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rangeShell_row_action (A : Matrix ι ι ℝ) (g : ℕ → Matrix ι ι ℝ)
    (hg : ∀ m, IsMoorePenroseInverse (A ^ m) (g m)) (x : ι → ℝ) (m : ℕ) :
    ((x ᵥ* rangeShell A g m) ᵥ* A ^ (m + 1) = 0) ∧
    (((x ᵥ* rangeShell A g m) ᵥ* A ^ m = 0) ↔ x ᵥ* rangeShell A g m = 0) := by
  constructor
  · rw [vecMul_vecMul, rangeShell_mul_pow_eq_zero A g hg (le_refl (m + 1))]
    simp
  · constructor
    · intro hx
      calc
        x ᵥ* rangeShell A g m = ((x ᵥ* rangeShell A g m) ᵥ* A ^ m) ᵥ* g m := by
          simp only [vecMul_vecMul, rangeShell_recovery A g hg m]
        _ = 0 := by rw [hx]; simp
    · intro hx
      rw [hx]
      simp

theorem deathShell_column_action (A : Matrix ι ι ℝ) (g : ℕ → Matrix ι ι ℝ)
    (hg : ∀ m, IsMoorePenroseInverse (A ^ m) (g m)) (x : ι → ℝ) (m : ℕ) :
    (A ^ (m + 1) *ᵥ (deathShell A g m *ᵥ x) = 0) ∧
    ((A ^ m *ᵥ (deathShell A g m *ᵥ x) = 0) ↔ deathShell A g m *ᵥ x = 0) := by
  constructor
  · rw [mulVec_mulVec, pow_mul_deathShell_eq_zero A g hg (le_refl (m + 1))]
    simp
  · constructor
    · intro hx
      have hrec : g m *ᵥ (A ^ m *ᵥ (deathShell A g m *ᵥ x)) = deathShell A g m *ᵥ x := by
        simpa only [← mulVec_mulVec] using
          congrArg (fun B : Matrix ι ι ℝ => B *ᵥ x) (deathShell_recovery A g hg m)
      rw [← hrec, hx]
      simp
    · intro hx
      rw [hx]
      simp

theorem dressedShell_row_action {A D : Matrix ι ι ℝ} {k : ℕ}
    (hD : IsDrazinInverse A D k) (g : ℕ → Matrix ι ι ℝ)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent A D ^ m) (g m))
    (x : ι → ℝ) (m : ℕ) :
    ((x ᵥ* dressedShell A D g m) ᵥ* A ^ (m + 1) = 0) ∧
    (((x ᵥ* dressedShell A D g m) ᵥ* A ^ m = 0) ↔
      x ᵥ* dressedShell A D g m = 0) := by
  constructor
  · rw [vecMul_vecMul, dressedShell_mul_pow_succ hD hg m]
    simp
  · constructor
    · intro hx
      calc
        x ᵥ* dressedShell A D g m =
            ((x ᵥ* dressedShell A D g m) ᵥ* A ^ m) ᵥ*
              (g m * complementaryProjection A D) := by
          simp only [vecMul_vecMul, dressedShell_recovery hD hg m]
        _ = 0 := by rw [hx]; simp
    · intro hx
      rw [hx]
      simp

/-- An invertible one-dimensional core coupled to a length-two nilpotent block. -/
def obliqueA : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 0, 0, 1; 0, 0, 0]
def obliqueD : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 1; 0, 0, 0; 0, 0, 0]
def obliqueN : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, -1; 0, 0, 1; 0, 0, 0]
def obliqueM : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; -1/2, 1/2, 0]

def obliquePowers : ℕ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => 1
  | 1 => obliqueM
  | _ + 2 => 0

theorem oblique_drazin : IsDrazinInverse obliqueA obliqueD 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [obliqueA, obliqueD, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem oblique_nilpotent : nilpotent obliqueA obliqueD = obliqueN := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotent, core, obliqueA, obliqueD, obliqueN,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem obliqueN_sq : obliqueN ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliqueN, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem oblique_mp : IsMoorePenroseInverse obliqueN obliqueM := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [obliqueN, obliqueM, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [obliqueN, obliqueM, Matrix.mul_apply, Fin.sum_univ_succ]
  · change (obliqueN * obliqueM).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [obliqueN, obliqueM, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · change (obliqueM * obliqueN).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [obliqueN, obliqueM, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_succ]

theorem oblique_mp_family (m : ℕ) :
    IsMoorePenroseInverse (nilpotent obliqueA obliqueD ^ m) (obliquePowers m) := by
  rw [oblique_nilpotent]
  cases m with
  | zero => simp [obliquePowers, IsMoorePenroseInverse]
  | succ m =>
    cases m with
    | zero => simpa [obliquePowers] using oblique_mp
    | succ m =>
      have hp : obliqueN ^ (m + 1 + 1) = 0 := by
        rw [show m + 1 + 1 = 2 + m by omega, pow_add, obliqueN_sq, zero_mul]
      rw [hp]
      simp [obliquePowers, IsMoorePenroseInverse]

theorem oblique_shell_zero :
    dressedShell obliqueA obliqueD obliquePowers 0 =
      !![0, 0, -1/2; 0, 0, -1/2; 0, 0, 1] := by
  unfold dressedShell rangeShell
  simp only [oblique_nilpotent, pow_zero, pow_one, obliquePowers]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complementaryProjection, projection, obliqueA, obliqueD, obliqueN,
      obliqueM, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem oblique_shell_one :
    dressedShell obliqueA obliqueD obliquePowers 1 =
      !![0, -1, -1/2; 0, 1, 1/2; 0, 0, 0] := by
  unfold dressedShell rangeShell
  simp only [oblique_nilpotent, pow_one, obliquePowers]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complementaryProjection, projection, obliqueA, obliqueD, obliqueN,
      obliqueM, pow_succ, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem oblique_shell_zero_not_selfAdjoint :
    ¬ IsSelfAdjoint (dressedShell obliqueA obliqueD obliquePowers 0) := by
  rw [oblique_shell_zero]
  intro h
  have he := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℝ => B 0 2) h.star_eq
  change ( !![0, 0, -1/2; 0, 0, -1/2; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).conjTranspose 0 2 = _ at he
  norm_num [Matrix.conjTranspose_apply] at he

/-- Reversing the action invalidates the one-step extinction assertion. -/
theorem oblique_action_asymmetry :
    dressedShell obliqueA obliqueD obliquePowers 0 * obliqueA = 0 ∧
    obliqueA * dressedShell obliqueA obliqueD obliquePowers 0 ≠ 0 := by
  constructor
  · simpa using dressedShell_mul_pow_succ oblique_drazin oblique_mp_family 0
  · rw [oblique_shell_zero]
    intro h
    have he := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℝ => B 0 2) h
    norm_num [obliqueA, Matrix.mul_apply, Fin.sum_univ_succ] at he

end InfoGeometry.Canonical.DrazinShellMatrixAction
