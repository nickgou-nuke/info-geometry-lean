/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionKMSState
import InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
import InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
import Mathlib.Tactic

/-!
# Finite attention states on the canonical matrix tower

This module transports one finite softmax state to the selected dyadic
matrix stage and then uses the repository-owned noncommutative matrix
direct-limit functional. It proves only the selected-stage state and its
colimit extension. It makes no claim of compatibility between independently
chosen logits at different stages, nor of a colimit modular flow.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionStageColimitState

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges

/-- Entrywise complexification of a real matrix, retaining its full matrix
carrier and multiplication structure. -/
def complexifyRealMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  fun i j => (A i j : ℂ)

/-- The attention density at tower stage `k`, scaled by the matrix dimension.
The scaling compensates for the tower's normalized trace `(2^k)⁻¹ Tr`. -/
def attentionStageDensity (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    MatrixStage k :=
  Matrix.diagonal (fun i => (2 ^ k : ℂ) *
    (softmaxWeight logits β i : ℂ))

@[simp]
theorem attentionStageDensity_apply (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (i j : Fin (2 ^ k)) :
    attentionStageDensity k logits β i j =
      if i = j then (2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ) else 0 := by
  rw [attentionStageDensity, Matrix.diagonal_apply]

/-- The seed density is the dimension-scaled complexification of the existing
real attention density matrix. -/
theorem attentionStageDensity_eq_scaled_complexification (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    attentionStageDensity k logits β =
      (2 ^ k : ℂ) • complexifyRealMatrix
        (attentionDensityMatrix logits β) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [attentionStageDensity, complexifyRealMatrix, attentionDensityMatrix]
  · simp [attentionStageDensity, complexifyRealMatrix, attentionDensityMatrix,
      hij]

/-- The selected seed density has normalized matrix trace one. -/
theorem attentionStageDensity_normalizedTrace (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    matrixTraceFunctional k (attentionStageDensity k logits β) = 1 := by
  rw [matrixTraceFunctional_apply]
  rw [show Matrix.trace (attentionStageDensity k logits β) =
      (2 ^ k : ℂ) by
    rw [attentionStageDensity, Matrix.trace_diagonal]
    have hsum : (∑ i : Fin (2 ^ k),
        (2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ)) =
        (2 ^ k : ℂ) * 1 := by
      calc
        (∑ i : Fin (2 ^ k),
            (2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ)) =
            (2 ^ k : ℂ) * ∑ i : Fin (2 ^ k),
              (softmaxWeight logits β i : ℂ) := by
                rw [← Finset.mul_sum]
        _ = (2 ^ k : ℂ) * ((∑ i : Fin (2 ^ k),
              softmaxWeight logits β i : ℝ) : ℂ) := by
                congr 1
                change (∑ i : Fin (2 ^ k),
                  (algebraMap ℝ ℂ) (softmaxWeight logits β i)) =
                  (algebraMap ℝ ℂ) (∑ i : Fin (2 ^ k),
                    softmaxWeight logits β i)
                exact (map_sum (algebraMap ℝ ℂ)
                  (fun i : Fin (2 ^ k) => softmaxWeight logits β i)
                  Finset.univ).symm
        _ = (2 ^ k : ℂ) * 1 := by
                rw [softmaxWeight_sum_one]
                simp
    simpa using hsum]
  have hne : (2 ^ k : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero k (by norm_num)
  exact one_div_mul_cancel hne

/-- The finite attention seed is Hermitian as a complex matrix. -/
theorem attentionStageDensity_hermitian (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    (attentionStageDensity k logits β).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [attentionStageDensity]
  · rw [attentionStageDensity_apply, attentionStageDensity_apply]
    have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

/-- The finite attention seed is positive as a full complex matrix. -/
theorem attentionStageDensity_positive (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    ComplexPositive (attentionStageDensity k logits β) := by
  intro v
  have hdiag :
      (∑ i : Fin (2 ^ k), ∑ j : Fin (2 ^ k),
        star (v i) * attentionStageDensity k logits β i j * v j) =
      ((∑ i : Fin (2 ^ k),
        ((2 ^ k : ℝ) * softmaxWeight logits β i) *
          Complex.normSq (v i) : ℝ) : ℂ) := by
    classical
    have hterm (i : Fin (2 ^ k)) :
        star (v i) * ((2 ^ k : ℂ) *
            (softmaxWeight logits β i : ℂ)) * v i =
          (((2 ^ k : ℝ) * softmaxWeight logits β i) *
            Complex.normSq (v i) : ℝ) := by
      calc
        star (v i) * ((2 ^ k : ℂ) *
            (softmaxWeight logits β i : ℂ)) * v i =
            ((2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ)) *
              (star (v i) * v i) := by ring
        _ = ((2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ)) *
              (Complex.normSq (v i) : ℂ) := by
                have hnorm : star (v i) * v i =
                    (Complex.normSq (v i) : ℂ) := by
                  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
                rw [hnorm]
        _ = (((2 ^ k : ℝ) * softmaxWeight logits β i) *
              Complex.normSq (v i) : ℝ) := by
                push_cast
                ring
    calc
      (∑ i : Fin (2 ^ k), ∑ j : Fin (2 ^ k),
          star (v i) * attentionStageDensity k logits β i j * v j) =
          ∑ i : Fin (2 ^ k),
            star (v i) * ((2 ^ k : ℂ) *
              (softmaxWeight logits β i : ℂ)) * v i := by
                simp_rw [attentionStageDensity_apply]
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_eq_single i]
                · simp
                · intro j hj hji
                  simp [Ne.symm hji]
                · simp
      _ = ((∑ i : Fin (2 ^ k),
            ((2 ^ k : ℝ) * softmaxWeight logits β i) *
              Complex.normSq (v i) : ℝ) : ℂ) := by
                have hcast :
                    ((∑ i : Fin (2 ^ k),
                      ((2 ^ k : ℝ) * softmaxWeight logits β i) *
                        Complex.normSq (v i) : ℝ) : ℂ) =
                      ∑ i : Fin (2 ^ k),
                        ((((2 ^ k : ℝ) * softmaxWeight logits β i) *
                          Complex.normSq (v i) : ℝ) : ℂ) :=
                  map_sum (algebraMap ℝ ℂ)
                    (fun i : Fin (2 ^ k) =>
                      ((2 ^ k : ℝ) * softmaxWeight logits β i) *
                        Complex.normSq (v i)) Finset.univ
                rw [hcast]
                exact Finset.sum_congr rfl (fun i _ => hterm i)
  rw [hdiag, Complex.ofReal_re]
  apply Finset.sum_nonneg
  intro i hi
  have hweight : 0 ≤ softmaxWeight logits β i :=
    le_of_lt (softmaxWeight_pos logits β i)
  have hnorm : 0 ≤ Complex.normSq (v i) := Complex.normSq_nonneg _
  exact mul_nonneg (mul_nonneg (by positivity) hweight) hnorm

/-- The finite attention seed defines a unital functional on the canonical
noncommutative matrix direct limit. -/
theorem attentionColimitFunctional_unital (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
      (1 : Carrier) = 1 := by
  apply selectedStageColimitFunctional_one
  exact attentionStageDensity_normalizedTrace k logits β

/-- The resulting colimit functional is nonnegative on star-squares. -/
theorem attentionColimitFunctional_starSquare_nonneg (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (x : Carrier) :
    0 ≤ (selectedStageColimitFunctional k (attentionStageDensity k logits β)
      (star x * x)).re := by
  apply selectedStageColimitFunctional_positive
  exact attentionStageDensity_positive k logits β

/-- Star-square values of the attention colimit functional are real. -/
theorem attentionColimitFunctional_starSquare_im_zero (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (x : Carrier) :
    (selectedStageColimitFunctional k (attentionStageDensity k logits β)
      (star x * x)).im = 0 := by
  apply selectedStageColimitFunctional_starSquare_im_zero
  exact attentionStageDensity_hermitian k logits β

/-- At the chosen stage the functional reads out the normalized weighted
trace against the scaled complexified attention density. -/
theorem attentionColimitFunctional_seed_readout (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (A : MatrixStage k) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
      (stageInjection k A) =
        matrixTraceFunctional k (A * attentionStageDensity k logits β) := by
  exact selectedStageColimitFunctional_stage k _ A

/-- Exact real-observable readout at the selected stage: after entrywise
complexification, the tower state agrees with the original finite attention
state on every full real matrix observable. -/
theorem attentionColimitFunctional_real_seed_readout (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
      (stageInjection k (complexifyRealMatrix A)) =
        (attentionState logits β A : ℂ) := by
  rw [attentionColimitFunctional_seed_readout]
  rw [matrixTraceFunctional_apply]
  have htrace :
      Matrix.trace (complexifyRealMatrix A * attentionStageDensity k logits β) =
        (2 ^ k : ℂ) * (attentionState logits β A : ℂ) := by
    classical
    have hstate :
        (attentionState logits β A : ℂ) =
          ∑ i : Fin (2 ^ k),
            ((softmaxWeight logits β i * A i i : ℝ) : ℂ) := by
      rw [attentionState_eq_sum]
      exact map_sum (algebraMap ℝ ℂ)
        (fun i : Fin (2 ^ k) => softmaxWeight logits β i * A i i)
        Finset.univ
    calc
      Matrix.trace (complexifyRealMatrix A * attentionStageDensity k logits β) =
          ∑ i : Fin (2 ^ k),
            (A i i : ℂ) *
              ((2 ^ k : ℂ) * (softmaxWeight logits β i : ℂ)) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          complexifyRealMatrix, attentionStageDensity_apply]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · simp
        · intro j hj hji
          simp [hji]
        · simp
      _ = (2 ^ k : ℂ) *
            (∑ i : Fin (2 ^ k),
              ((softmaxWeight logits β i * A i i : ℝ) : ℂ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        push_cast
        ac_rfl
      _ = (2 ^ k : ℂ) * (attentionState logits β A : ℂ) := by
        rw [hstate]
  rw [htrace]
  have hne : (2 ^ k : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero k (by norm_num)
  calc
    (1 / (2 ^ k : ℂ)) * ((2 ^ k : ℂ) * (attentionState logits β A : ℂ)) =
        ((1 / (2 ^ k : ℂ)) * (2 ^ k : ℂ)) *
          (attentionState logits β A : ℂ) := by rw [← mul_assoc]
    _ = attentionState logits β A := by
      rw [one_div_mul_cancel hne]
      simp

end InfoGeometry.QuantumContext.AttentionStageColimitState

end
