/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real Finset Matrix

namespace KuboMoriBogoliubov

variable {n : ℕ}

/-- Faithful Quantum Density State ρ = diag(p₁, ..., pₙ) with strictly positive eigenvalues p_i > 0. -/
structure FaithfulDensityState (n : Type*) [Fintype n] [DecidableEq n] where
  eigenvalues : n → ℝ
  p_pos : ∀ i, 0 < eigenvalues i
  p_sum : ∑ i : n, eigenvalues i = 1

namespace FaithfulDensityState

variable {n : Type*} [Fintype n] [DecidableEq n] (rho : FaithfulDensityState n)

/-- Logarithmic Mean Weight c(p_i, p_j) for Kubo-Mori-Bogoliubov Metric.
    c(p_i, p_j) = (p_i - p_j) / (ln p_i - ln p_j) for p_i ≠ p_j, and p_i for p_i = p_j. -/
def bkmWeight (i j : n) : ℝ :=
  if rho.eigenvalues i = rho.eigenvalues j then
    rho.eigenvalues i
  else
    (rho.eigenvalues i - rho.eigenvalues j) / (Real.log (rho.eigenvalues i) - Real.log (rho.eigenvalues j))

/-- **Theorem**: BKM Weight Symmetry: c(p_i, p_j) = c(p_j, p_i). -/
theorem bkm_weight_symmetric (i j : n) :
    rho.bkmWeight i j = rho.bkmWeight j i := by
  dsimp [bkmWeight]
  by_cases h : rho.eigenvalues i = rho.eigenvalues j
  · have h_rev : rho.eigenvalues j = rho.eigenvalues i := h.symm
    rw [ite_eq_left h, ite_eq_left h_rev, h]
  · have h_rev : ¬(rho.eigenvalues j = rho.eigenvalues i) := fun h_eq => h h_eq.symm
    rw [ite_eq_right h, ite_eq_right h_rev]
    have h_num : rho.eigenvalues i - rho.eigenvalues j = - (rho.eigenvalues j - rho.eigenvalues i) := by ring
    have h_den : Real.log (rho.eigenvalues i) - Real.log (rho.eigenvalues j) = - (Real.log (rho.eigenvalues j) - Real.log (rho.eigenvalues i)) := by ring
    rw [h_num, h_den, neg_div_neg_eq]

/-- Faithfulness makes every logarithmic-mean coefficient strictly positive,
including the off-diagonal spectral coefficients. -/
theorem bkm_weight_pos (i j : n) : 0 < rho.bkmWeight i j := by
  by_cases h : rho.eigenvalues i = rho.eigenvalues j
  · dsimp [bkmWeight]
    rw [ite_eq_left h]
    exact rho.p_pos i
  · dsimp [bkmWeight]
    rw [ite_eq_right h]
    rcases lt_or_gt_of_ne h with h_lt | h_gt
    · exact div_pos_of_neg_of_neg
        (sub_neg.mpr h_lt)
        (sub_neg.mpr (Real.log_lt_log (rho.p_pos i) h_lt))
    · exact div_pos
        (sub_pos.mpr h_gt)
        (sub_pos.mpr (Real.log_lt_log (rho.p_pos j) h_gt))

/-- Genuine Kubo-Mori-Bogoliubov (BKM) Inner Product on Matrix Operators:
    <A, B>_{BKM, ρ} = ∑_{i, j} A_ji * B_ji * c(p_i, p_j). -/
def bkmInnerProduct (A B : Matrix n n ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, A j i * B j i * rho.bkmWeight i j

/-- **Theorem**: Genuine BKM Metric Symmetry: <A, B>_{BKM, ρ} = <B, A>_{BKM, ρ}. -/
theorem bkm_metric_symmetry (A B : Matrix n n ℝ) :
    rho.bkmInnerProduct A B = rho.bkmInnerProduct B A := by
  dsimp [bkmInnerProduct]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [rho.bkm_weight_symmetric i j]
  calc
    A j i * B j i * rho.bkmWeight j i =
        (A j i * B j i) * rho.bkmWeight j i := by rw [mul_assoc]
    _ = (B j i * A j i) * rho.bkmWeight j i := by rw [mul_comm (A j i) (B j i)]
    _ = B j i * A j i * rho.bkmWeight j i := by rw [mul_assoc]

/-- The BKM quadratic form is nonnegative on every real matrix observable. -/
theorem bkm_metric_pos_semidef (A : Matrix n n ℝ) :
    0 ≤ rho.bkmInnerProduct A A := by
  dsimp [bkmInnerProduct]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have h_sq : 0 ≤ (A j i) ^ 2 := sq_nonneg (A j i)
  have h_prod : A j i * A j i * rho.bkmWeight i j = (A j i) ^ 2 * rho.bkmWeight i j := by ring
  rw [h_prod]
  exact mul_nonneg h_sq (le_of_lt (rho.bkm_weight_pos i j))

/-- Strict positive definiteness of the faithful-state BKM form on all matrix
observables: zero quadratic form forces every matrix entry to vanish. -/
theorem bkm_metric_pos_def (A : Matrix n n ℝ) :
    rho.bkmInnerProduct A A = 0 ↔ A = 0 := by
  constructor
  · intro hzero
    by_contra hA
    have h_entry : ∃ i j, A j i ≠ 0 := by
      by_contra h
      push Not at h
      apply hA
      ext i j
      exact h j i
    obtain ⟨i₀, j₀, h_entry⟩ := h_entry
    have h_inner_nonneg (i : n) :
        0 ≤ ∑ j, A j i * A j i * rho.bkmWeight i j := by
      apply Finset.sum_nonneg
      intro j _
      have h_prod : A j i * A j i * rho.bkmWeight i j =
          (A j i) ^ 2 * rho.bkmWeight i j := by ring
      rw [h_prod]
      exact mul_nonneg (sq_nonneg _) (le_of_lt (rho.bkm_weight_pos i j))
    have h_inner_pos :
        0 < ∑ j, A j i₀ * A j i₀ * rho.bkmWeight i₀ j := by
      apply Finset.sum_pos'
      · intro j _
        have h_prod : A j i₀ * A j i₀ * rho.bkmWeight i₀ j =
            (A j i₀) ^ 2 * rho.bkmWeight i₀ j := by ring
        rw [h_prod]
        exact mul_nonneg (sq_nonneg _) (le_of_lt (rho.bkm_weight_pos i₀ j))
      · have h_prod : A j₀ i₀ * A j₀ i₀ * rho.bkmWeight i₀ j₀ =
            (A j₀ i₀) ^ 2 * rho.bkmWeight i₀ j₀ := by ring
        refine ⟨j₀, Finset.mem_univ _, ?_⟩
        rw [h_prod]
        exact mul_pos (sq_pos_of_ne_zero h_entry) (rho.bkm_weight_pos i₀ j₀)
    have h_total_pos :
        0 < ∑ i, ∑ j, A j i * A j i * rho.bkmWeight i j := by
      apply Finset.sum_pos'
      · intro i _
        exact h_inner_nonneg i
      · exact ⟨i₀, Finset.mem_univ _, h_inner_pos⟩
    dsimp [bkmInnerProduct] at hzero
    exact (ne_of_gt h_total_pos) hzero
  · rintro rfl
    simp [bkmInnerProduct]

end FaithfulDensityState

end KuboMoriBogoliubov
