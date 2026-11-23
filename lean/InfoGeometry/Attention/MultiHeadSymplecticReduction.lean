/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Attention.MetriplecticAttentionDynamics
import InfoGeometry.Attention.SymplecticDefectInvariance

namespace InfoGeometry.Attention.MultiHeadSymplecticReduction

open Matrix
open InfoGeometry.Attention.MetriplecticAttentionDynamics

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

def _witness_m1 : Mat2R := Matrix.single 0 1 1
def _witness_m2 : Mat2R := Matrix.single 1 0 1

theorem _witness_noncommute : _witness_m1 * _witness_m2 ≠ _witness_m2 * _witness_m1 := by
  intro h
  have h₁ : _witness_m1 * _witness_m2 = Matrix.single 0 0 (1 : ℝ) := by
    simp [_witness_m1, _witness_m2, Matrix.single_mul_single_same]
  have h₂ : _witness_m2 * _witness_m1 = Matrix.single 1 1 (1 : ℝ) := by
    simp [_witness_m1, _witness_m2, Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h₃ := congrFun (congrFun h 0) 0
  norm_num at h₃

theorem mat2R_noncommutative_witness :
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ) * (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) ℝ) ≠
    (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) ℝ) * (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have hMK : (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ) * (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.single 0 0 (1 : ℝ) := by
    simp [Matrix.single_mul_single_same]
  have hKM : (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) ℝ) * (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.single 1 1 (1 : ℝ) := by
    simp [Matrix.single_mul_single_same]
  rw [hMK, hKM] at h
  have h00 := congrFun (congrFun h 0) 0
  norm_num at h00

/-!
# Archetype 907: Multi-Head Symplectic Reduction and Infinitesimal Symplectic Gating

This module proves that the chiral bipolar attention channel and the Dirac grading
operator both belong to the infinitesimal symplectic Lie algebra 𝔰𝔭(2, ℝ), preserving
the canonical symplectic structure J = !![0, 1; -1, 0].
-/

/-- The standard canonical symplectic matrix J on ℝ²: J² = -1. -/
def J_symp : Mat2R :=
  InfoGeometry.Attention.SymplecticDefectInvariance.J_symp

/-- Master Theorem 1: J is a complex structure: J² = -1. -/
theorem J_symp_sq : J_symp * J_symp = - (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J_symp, InfoGeometry.Attention.SymplecticDefectInvariance.J_symp,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Master Theorem 2: J is skew-symmetric: Jᵀ = -J. -/
theorem J_symp_skew : J_sympᵀ = - J_symp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J_symp, InfoGeometry.Attention.SymplecticDefectInvariance.J_symp,
      transpose_apply]

/-- The Dirac grading is an infinitesimal symplectic generator. -/
theorem G_is_infinitesimal_symplectic :
    G_gradingᵀ * J_symp + J_symp * G_grading = 0 := by
  change G_gradingᵀ * InfoGeometry.Attention.SymplecticDefectInvariance.J_symp +
    InfoGeometry.Attention.SymplecticDefectInvariance.J_symp * G_grading = 0
  rw [InfoGeometry.Attention.SymplecticDefectInvariance.traceless_iff_infinitesimal_symplectic]
  simp [Matrix.trace, G_grading, Fin.sum_univ_two]

/-- Every off-diagonal chiral bipolar matrix is infinitesimal symplectic; no
balance condition on its two off-diagonal entries is needed in dimension two. -/
theorem chiral_bipolar_is_infinitesimal_symplectic (M : Mat2R) :
    (chiral_bipolar M)ᵀ * J_symp + J_symp * chiral_bipolar M = 0 := by
  change (chiral_bipolar M)ᵀ * InfoGeometry.Attention.SymplecticDefectInvariance.J_symp +
    InfoGeometry.Attention.SymplecticDefectInvariance.J_symp * chiral_bipolar M = 0
  rw [InfoGeometry.Attention.SymplecticDefectInvariance.traceless_iff_infinitesimal_symplectic]
  simp [Matrix.trace, chiral_bipolar, Fin.sum_univ_two]

/-- Master Theorem 5: The total Dirac Hamiltonian H = p • G + C(M) is infinitesimal symplectic.
    It preserves the canonical symplectic form on the latent phase space. -/
theorem dirac_hamiltonian_is_infinitesimal_symplectic (M : Mat2R) (p : ℝ)
    :
    (p • G_grading + chiral_bipolar M)ᵀ * J_symp +
      J_symp * (p • G_grading + chiral_bipolar M) = 0 := by
  have hG := G_is_infinitesimal_symplectic
  have hC := chiral_bipolar_is_infinitesimal_symplectic M
  calc (p • G_grading + chiral_bipolar M)ᵀ * J_symp + J_symp * (p • G_grading + chiral_bipolar M)
      = (p • G_gradingᵀ + (chiral_bipolar M)ᵀ) * J_symp + (J_symp * (p • G_grading) + J_symp * chiral_bipolar M) := by
        simp only [transpose_add, transpose_smul, mul_add]
    _ = (p • (G_gradingᵀ * J_symp) + (chiral_bipolar M)ᵀ * J_symp) +
        (p • (J_symp * G_grading) + J_symp * chiral_bipolar M) := by
        simp only [add_mul, Matrix.smul_mul, Matrix.mul_smul]
    _ = p • (G_gradingᵀ * J_symp + J_symp * G_grading) +
        ((chiral_bipolar M)ᵀ * J_symp + J_symp * chiral_bipolar M) := by
        simp only [smul_add]
        abel
    _ = p • (0 : Mat2R) + 0 := by rw [hG, hC]
    _ = 0 := by simp

/-- The symplectic Lie algebra condition: Kᵀ * J + J * K = 0. -/
def is_infinitesimal_symplectic (K : Mat2R) : Prop :=
  Kᵀ * J_symp + J_symp * K = 0

end InfoGeometry.Attention.MultiHeadSymplecticReduction
