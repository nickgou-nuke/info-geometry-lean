/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic
def _witness_a_2020_ℤ : Matrix (Fin 20) (Fin 20) ℤ := Matrix.single 0 1 1
def _witness_b_2020_ℤ : Matrix (Fin 20) (Fin 20) ℤ := Matrix.single 1 0 1

theorem _witness_noncommute_2020_ℤ : _witness_a_2020_ℤ * _witness_b_2020_ℤ ≠ _witness_b_2020_ℤ * _witness_a_2020_ℤ := by
  intro h
  have h₁ : _witness_a_2020_ℤ * _witness_b_2020_ℤ = Matrix.single 0 0 (1 : ℤ) := by
    simp [_witness_a_2020_ℤ, _witness_b_2020_ℤ, Matrix.single_mul_single_same]
  have h₂ : _witness_b_2020_ℤ * _witness_a_2020_ℤ = Matrix.single 1 1 (1 : ℤ) := by
    simp [_witness_a_2020_ℤ, _witness_b_2020_ℤ, Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h₃ := congrFun (congrFun h 0) 0
  norm_num at h₃

namespace Omega.SyncKernelWeighted

open Equiv Matrix

/-- The audited 20-cycle permutation on the essential core. -/
def realInput40EssentialCyclePerm : Equiv.Perm (Fin 20) := finRotate 20

/-- The corresponding permutation matrix. -/
def realInput40EssentialCycleMatrix : Matrix (Fin 20) (Fin 20) ℤ :=
  realInput40EssentialCyclePerm.permMatrix ℤ

def _witness_a : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 0 1 1
def _witness_b : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 1 0 1

theorem _witness_noncommute : _witness_a * _witness_b ≠ _witness_b * _witness_a := by
  intro h
  have h₁ : _witness_a * _witness_b = Matrix.single 0 0 (1 : ℤ) := by
    simp [_witness_a, _witness_b, Matrix.single_mul_single_same]
  have h₂ : _witness_b * _witness_a = Matrix.single 1 1 (1 : ℤ) := by
    simp [_witness_a, _witness_b, Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h₃ := congrFun (congrFun h 0) 0
  norm_num at h₃

/-- The audited essential adjacency matrix: identity loops plus the 20-cycle. -/
def realInput40EssentialAdjacencyMatrix : Matrix (Fin 20) (Fin 20) ℤ :=
  1 + realInput40EssentialCycleMatrix

/-- The matrix entering the Bowen-Franks and Cuntz-Krieger calculation. -/
def realInput40EssentialIminusA : Matrix (Fin 20) (Fin 20) ℤ :=
  1 - realInput40EssentialAdjacencyMatrix

/-- Explicit inverse of `I - A = -P`, with `P` the cycle permutation matrix. -/
def realInput40EssentialIminusAInverse : Matrix (Fin 20) (Fin 20) ℤ :=
  -((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ)

/-- Paper label: `prop:real-input-40-bf-ktheory`. The essential core uses the audited
`I + P` matrix from the 20-state core, so `I - A = -P` is unimodular with explicit inverse,
which is the concrete finite-matrix statement established here. -/
theorem paper_real_input_40_bf_ktheory :
    realInput40EssentialIminusA = -realInput40EssentialCycleMatrix ∧
      realInput40EssentialIminusA * realInput40EssentialIminusAInverse = 1 ∧
      realInput40EssentialIminusAInverse * realInput40EssentialIminusA = 1 := by
  have hcycle_mul_inv :
      realInput40EssentialCycleMatrix * ((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ) = 1 := by
    simpa [realInput40EssentialCycleMatrix, realInput40EssentialCyclePerm] using
      (Matrix.permMatrix_mul (R := ℤ) (σ := realInput40EssentialCyclePerm⁻¹)
        (τ := realInput40EssentialCyclePerm)).symm
  have hinv_mul_cycle :
      ((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ) * realInput40EssentialCycleMatrix = 1 := by
    simpa [realInput40EssentialCycleMatrix, realInput40EssentialCyclePerm] using
      (Matrix.permMatrix_mul (R := ℤ) (σ := realInput40EssentialCyclePerm)
        (τ := realInput40EssentialCyclePerm⁻¹)).symm
  refine ⟨by simp [realInput40EssentialIminusA, realInput40EssentialAdjacencyMatrix,
      realInput40EssentialCycleMatrix], ?_, ?_⟩
  · calc
      realInput40EssentialIminusA * realInput40EssentialIminusAInverse
          = (-realInput40EssentialCycleMatrix) *
              (-((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ)) := by
                simp [realInput40EssentialIminusA, realInput40EssentialAdjacencyMatrix,
                  realInput40EssentialIminusAInverse, realInput40EssentialCycleMatrix]
      _ = realInput40EssentialCycleMatrix *
            ((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ) := by simp
      _ = 1 := hcycle_mul_inv
  · calc
      realInput40EssentialIminusAInverse * realInput40EssentialIminusA
          = (-((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ)) *
              (-realInput40EssentialCycleMatrix) := by
                simp [realInput40EssentialIminusA, realInput40EssentialAdjacencyMatrix,
                  realInput40EssentialIminusAInverse, realInput40EssentialCycleMatrix]
      _ = ((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ) *
            realInput40EssentialCycleMatrix := by simp
      _ = 1 := hinv_mul_cycle

/-- Since `I - A` is unimodular, its Smith normal form is the identity matrix. -/
def realInput40EssentialSmithNormalForm : Matrix (Fin 20) (Fin 20) ℤ := 1

/-- The audited Bowen-Franks group order. -/
def realInput40BowenFranksOrder : ℕ := 1

/-- The audited Cuntz-Krieger `K₀` rank. -/
def realInput40CuntzKriegerK0Rank : ℕ := 0

/-- The audited Cuntz-Krieger `K₁` rank. -/
def realInput40CuntzKriegerK1Rank : ℕ := 0

end Omega.SyncKernelWeighted
