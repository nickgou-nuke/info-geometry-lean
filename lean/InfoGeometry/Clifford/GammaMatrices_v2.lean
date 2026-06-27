import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Concrete `Cl(1,1)` gamma witness

This file replaces the earlier placeholder generalization with an explicit,
kernel-checkable split-Clifford witness package:

- two concrete `2 × 2` generators over `ℝ`,
- their squares,
- their anticommutation law.

The general recursive `Cl(p,q)` construction lives in
`InfoGeometry.Clifford.GammaMatrices`; this file keeps the finite base case
honest and explicit.
-/

noncomputable section

namespace InfoGeometry.Clifford.GammaMatrices_v2

open Matrix

/-- First split-Clifford generator for `Cl(1,1)`. -/
def gamma₁ : Matrix (Fin 2) (Fin 2) ℝ :=
  fun
    | 0, 0 => 0
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 1 => 0

/-- Second split-Clifford generator for `Cl(1,1)`. -/
def gamma₂ : Matrix (Fin 2) (Fin 2) ℝ :=
  fun
    | 0, 0 => 0
    | 0, 1 => -1
    | 1, 0 => 1
    | 1, 1 => 0

@[simp] theorem gamma₁_sq : gamma₁ * gamma₁ = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [gamma₁, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem gamma₂_sq : gamma₂ * gamma₂ = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [gamma₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem gamma₁_gamma₂_anticomm :
    gamma₁ * gamma₂ + gamma₂ * gamma₁ = 0 := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [gamma₁, gamma₂, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two]

theorem gamma₂_gamma₁_anticomm :
    gamma₂ * gamma₁ + gamma₁ * gamma₂ = 0 := by
  simpa [add_comm] using gamma₁_gamma₂_anticomm

/--
Concrete witness package for the split `Cl(1,1)` base case.

This records the matrices together with their laws instead of hiding the
content behind a general placeholder.
-/
structure Cl11GammaWitness where
  Γ₁ : Matrix (Fin 2) (Fin 2) ℝ
  Γ₂ : Matrix (Fin 2) (Fin 2) ℝ
  Γ₁_sq : Γ₁ * Γ₁ = (1 : Matrix (Fin 2) (Fin 2) ℝ)
  Γ₂_sq : Γ₂ * Γ₂ = -(1 : Matrix (Fin 2) (Fin 2) ℝ)
  Γ_anticomm : Γ₁ * Γ₂ + Γ₂ * Γ₁ = 0

/-- The canonical `Cl(1,1)` witness. -/
def cl11GammaWitness : Cl11GammaWitness := by
  refine
    { Γ₁ := gamma₁
      Γ₂ := gamma₂
      Γ₁_sq := ?_
      Γ₂_sq := ?_
      Γ_anticomm := ?_ }
  · exact gamma₁_sq
  · exact gamma₂_sq
  · exact gamma₁_gamma₂_anticomm

@[simp] theorem cl11GammaWitness_Gamma₁ : cl11GammaWitness.Γ₁ = gamma₁ := rfl
@[simp] theorem cl11GammaWitness_Gamma₂ : cl11GammaWitness.Γ₂ = gamma₂ := rfl
@[simp] theorem cl11GammaWitness_Gamma₁_sq :
    cl11GammaWitness.Γ₁_sq = gamma₁_sq := rfl
@[simp] theorem cl11GammaWitness_Gamma₂_sq :
    cl11GammaWitness.Γ₂_sq = gamma₂_sq := rfl
@[simp] theorem cl11GammaWitness_Gamma_anticomm :
    cl11GammaWitness.Γ_anticomm = gamma₁_gamma₂_anticomm := rfl

end InfoGeometry.Clifford.GammaMatrices_v2
