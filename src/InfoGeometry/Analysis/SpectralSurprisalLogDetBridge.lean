/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic
import InfoGeometry.Analysis.LogDetSelfConcordantBarrier

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Analysis.SpectralSurprisalLogDetBridge

open Matrix
open InfoGeometry.Analysis.SelfConcordant

variable {n : ℕ}

def spectralSurprisal (vals : Fin n → ℝ) (i : Fin n) : ℝ :=
  -Real.log (vals i)

def surprisalDiagonal (vals : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (spectralSurprisal vals)

theorem exp_neg_spectralSurprisal
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) (i : Fin n) :
    Real.exp (-spectralSurprisal vals i) = vals i := by
  unfold spectralSurprisal
  rw [neg_neg, Real.exp_log (hpos i)]

theorem spectral_value_eq_exp_neg_surprisal
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) (i : Fin n) :
    vals i = Real.exp (-spectralSurprisal vals i) :=
  (exp_neg_spectralSurprisal vals hpos i).symm

theorem diagonal_eq_diagonal_exp_neg_surprisal
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) :
    Matrix.diagonal vals =
      Matrix.diagonal (fun i => Real.exp (-spectralSurprisal vals i)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [exp_neg_spectralSurprisal vals hpos]
  · simp [Matrix.diagonal, h]

theorem det_diagonal_spectrum (vals : Fin n → ℝ) :
    (Matrix.diagonal vals).det = ∏ i : Fin n, vals i :=
  Matrix.det_diagonal

theorem det_diagonal_spectrum_pos
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) :
    0 < (Matrix.diagonal vals).det := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_pos fun i _ => hpos i

theorem det_diagonal_spectrum_ne_zero
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) :
    (Matrix.diagonal vals).det ≠ 0 :=
  ne_of_gt (det_diagonal_spectrum_pos vals hpos)

theorem log_prod_spectrum
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) :
    Real.log (∏ i : Fin n, vals i) = ∑ i : Fin n, Real.log (vals i) := by
  apply Real.log_prod
  intro i hi
  exact ne_of_gt (hpos i)

theorem neg_log_det_diagonal_eq_sum_surprisal
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) :
    -Real.log ((Matrix.diagonal vals).det) =
      ∑ i : Fin n, spectralSurprisal vals i := by
  rw [Matrix.det_diagonal, log_prod_spectrum vals hpos]
  simp [spectralSurprisal]

theorem neg_log_prod_eq_sum_surprisal
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) :
    -Real.log (∏ i : Fin n, vals i) =
      ∑ i : Fin n, spectralSurprisal vals i := by
  rw [log_prod_spectrum vals hpos]
  simp [spectralSurprisal]

theorem det_diagonal_eq_exp_neg_sum_surprisal
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) :
    (Matrix.diagonal vals).det =
      Real.exp (-(∑ i : Fin n, spectralSurprisal vals i)) := by
  have hp : 0 < (Matrix.diagonal vals).det :=
    det_diagonal_spectrum_pos vals hpos
  have hlog := neg_log_det_diagonal_eq_sum_surprisal vals hpos
  calc
    (Matrix.diagonal vals).det =
        Real.exp (Real.log ((Matrix.diagonal vals).det)) := by
          symm
          exact Real.exp_log hp
    _ = Real.exp (-(∑ i : Fin n, spectralSurprisal vals i)) := by
      congr 1
      linarith

theorem prod_spectrum_eq_exp_neg_sum_surprisal
    (vals : Fin n → ℝ) (hpos : ∀ i, 0 < vals i) :
    ∏ i : Fin n, vals i =
      Real.exp (-(∑ i : Fin n, spectralSurprisal vals i)) := by
  rw [← Matrix.det_diagonal]
  exact det_diagonal_eq_exp_neg_sum_surprisal vals hpos

theorem logDetBarrier_eq_sum_spectralSurprisal
    (A : PosDefCone n) (vals : Fin n → ℝ)
    (hpos : ∀ i, 0 < vals i) (hdiag : A.mat = Matrix.diagonal vals) :
    phi A = ∑ i : Fin n, spectralSurprisal vals i := by
  unfold phi
  rw [hdiag]
  exact neg_log_det_diagonal_eq_sum_surprisal vals hpos

theorem trace_surprisalDiagonal (vals : Fin n → ℝ) :
    Matrix.trace (surprisalDiagonal vals) =
      ∑ i : Fin n, spectralSurprisal vals i := by
  unfold surprisalDiagonal
  rw [Matrix.trace_diagonal]

theorem logDetBarrier_eq_trace_surprisalDiagonal
    (A : PosDefCone n) (vals : Fin n → ℝ)
    (hpos : ∀ i, 0 < vals i) (hdiag : A.mat = Matrix.diagonal vals) :
    phi A = Matrix.trace (surprisalDiagonal vals) := by
  rw [trace_surprisalDiagonal]
  exact logDetBarrier_eq_sum_spectralSurprisal A vals hpos hdiag

theorem positive_diagonal_spectral_surprisal_chain
    (A : PosDefCone n) (vals : Fin n → ℝ)
    (hpos : ∀ i, 0 < vals i) (hdiag : A.mat = Matrix.diagonal vals) :
    (∀ i, vals i = Real.exp (-spectralSurprisal vals i)) ∧
    (A.mat.det = Real.exp (-(∑ i : Fin n, spectralSurprisal vals i))) ∧
    (phi A = ∑ i : Fin n, spectralSurprisal vals i) ∧
    (Matrix.trace (surprisalDiagonal vals) =
      ∑ i : Fin n, spectralSurprisal vals i) := by
  refine ⟨fun i => spectral_value_eq_exp_neg_surprisal vals hpos i, ?_, ?_, ?_⟩
  · rw [hdiag]
    exact det_diagonal_eq_exp_neg_sum_surprisal vals hpos
  · exact logDetBarrier_eq_sum_spectralSurprisal A vals hpos hdiag
  · exact trace_surprisalDiagonal vals

end InfoGeometry.Analysis.SpectralSurprisalLogDetBridge
