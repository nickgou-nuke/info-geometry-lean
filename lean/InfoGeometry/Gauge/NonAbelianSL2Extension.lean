/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Gauge.NonAbelianSL2Extension

open Complex Real Matrix

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def genJ : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, -1],
    ![1, 0]]

def genK : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0],
    ![0, -1]]

def genE : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1],
    ![0, 0]]

def genF : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 0],
    ![1, 0]]

theorem genJ_sq_eq_neg_one :
    genJ * genJ = - 1 := by
  ext i j
  change (∑ k : Fin 2, genJ i k * genJ k j) = (-1 : Matrix (Fin 2) (Fin 2) ℝ) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genJ, Matrix.one_apply, Fin.sum_univ_two]

theorem genK_sq_eq_one :
    genK * genK = 1 := by
  ext i j
  change (∑ k : Fin 2, genK i k * genK k j) = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genK, Matrix.one_apply, Fin.sum_univ_two]

theorem comm_K_E :
    genK * genE - genE * genK = (2 : ℝ) • genE := by
  ext i j
  change (∑ k : Fin 2, genK i k * genE k j) -
      (∑ k : Fin 2, genE i k * genK k j) = 2 * genE i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genK, genE, Fin.sum_univ_two]

theorem comm_K_F :
    genK * genF - genF * genK = -((2 : ℝ) • genF) := by
  ext i j
  change (∑ k : Fin 2, genK i k * genF k j) -
      (∑ k : Fin 2, genF i k * genK k j) = -(2 * genF i j)
  fin_cases i <;> fin_cases j <;>
    norm_num [genK, genF, Fin.sum_univ_two]

theorem comm_E_F :
    genE * genF - genF * genE = genK := by
  ext i j
  change (∑ k : Fin 2, genE i k * genF k j) -
      (∑ k : Fin 2, genF i k * genE k j) = genK i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genE, genF, genK, Fin.sum_univ_two]

/-! ## The complex `su(2)` matrix Lie algebra

The preceding real split generators model `sl₂(ℝ)`.  The following three
complex matrices instead give the compact real form: each is traceless and
skew-Hermitian, and their ordered commutator is nonzero. -/

def su2X : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, Complex.I], ![Complex.I, 0]]

def su2Y : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1], ![-1, 0]]

def su2Z : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![Complex.I, 0], ![0, -Complex.I]]

theorem su2X_trace : Matrix.trace su2X = 0 := by
  change (∑ i : Fin 2, su2X i i) = 0
  rw [Fin.sum_univ_two]
  norm_num [su2X]

theorem su2Y_trace : Matrix.trace su2Y = 0 := by
  change (∑ i : Fin 2, su2Y i i) = 0
  rw [Fin.sum_univ_two]
  norm_num [su2Y]

theorem su2Z_trace : Matrix.trace su2Z = 0 := by
  change (∑ i : Fin 2, su2Z i i) = 0
  rw [Fin.sum_univ_two]
  norm_num [su2Z]

theorem su2X_skewHermitian : su2Xᴴ = -su2X := by
  ext i j
  change star (su2X j i) = -su2X i j
  fin_cases i <;> fin_cases j <;>
    norm_num [su2X, Complex.conj_I]

theorem su2Y_skewHermitian : su2Yᴴ = -su2Y := by
  ext i j
  change star (su2Y j i) = -su2Y i j
  fin_cases i <;> fin_cases j <;>
    norm_num [su2Y]

theorem su2Z_skewHermitian : su2Zᴴ = -su2Z := by
  ext i j
  change star (su2Z j i) = -su2Z i j
  fin_cases i <;> fin_cases j <;>
    norm_num [su2Z, Complex.conj_I]

/-- The chosen normalization gives `[su2X,su2Y] = -2 su2Z`. -/
theorem su2X_su2Y_commutator :
    su2X * su2Y - su2Y * su2X = -((2 : ℂ) • su2Z) := by
  ext i j
  change (∑ k : Fin 2, su2X i k * su2Y k j) -
      (∑ k : Fin 2, su2Y i k * su2X k j) = -(2 * su2Z i j)
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [su2X, su2Y, su2Z] <;> ring

theorem su2Y_su2Z_commutator :
    su2Y * su2Z - su2Z * su2Y = -((2 : ℂ) • su2X) := by
  ext i j
  change (∑ k : Fin 2, su2Y i k * su2Z k j) -
      (∑ k : Fin 2, su2Z i k * su2Y k j) = -(2 * su2X i j)
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [su2X, su2Y, su2Z] <;> ring

theorem su2Z_su2X_commutator :
    su2Z * su2X - su2X * su2Z = -((2 : ℂ) • su2Y) := by
  ext i j
  change (∑ k : Fin 2, su2Z i k * su2X k j) -
      (∑ k : Fin 2, su2X i k * su2Z k j) = -(2 * su2Y i j)
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [su2X, su2Y, su2Z] <;> ring

/-- In particular the Lie algebra directions do not commute. -/
theorem su2X_su2Y_do_not_commute : su2X * su2Y ≠ su2Y * su2X := by
  intro h
  have hc : su2X * su2Y - su2Y * su2X = 0 := sub_eq_zero.mpr h
  rw [su2X_su2Y_commutator] at hc
  have hmat : (2 : ℂ) • su2Z = 0 := neg_eq_zero.mp hc
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hmat
  change (2 : ℂ) * Complex.I = 0 at hentry
  exact (mul_ne_zero (by norm_num) Complex.I_ne_zero) hentry

/-- The real `2 × 2` gauge generators do not commute either. -/
theorem real_sl2_generators_noncommute :
    ∃ matI matJ : Matrix (Fin 2) (Fin 2) ℝ,
      matI * matJ ≠ matJ * matI := by
  refine ⟨genJ, genK, ?_⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  change (∑ k : Fin 2, genJ 0 k * genK k 1) = (∑ k : Fin 2, genK 0 k * genJ k 1) at h01
  simp [genJ, genK, Fin.sum_univ_two] at h01
  norm_num at h01
