/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornReducedHistory
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHistoryRecoveryError
import InfoGeometry.Quantum.ReplacementStateChannel

/-! # Quantitative recovery obstruction for operator-valued Zorn channels

The partial trace is an additional loss of information after Peirce pinching.
The result applies to the full flattened matrix carrier and every decoder
of the complete reduced history, with a strictly positive uniform error bound.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornHistoryQuantitativeRecovery

open Matrix InfoGeometry.Physics.NCG InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHistoryRecoveryError
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornCoarseGrainedRecovery
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornReducedHistory
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteMarginal
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Quantum.ReplacementStateChannel
open scoped ComplexOrder MatrixOrder

variable {d : ℕ} [NeZero d]
local notation "Flat" => Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ
local notation "Sheet" => Matrix (Fin 2) (Fin 2) ℂ

/-- For a nonzero contractive operator-valued Zorn coefficient there is a
CPTP corner channel, a nonzero directed Kraus operator, and a fixed pair of
states whose identical reduced histories force a positive decoder-independent
lower bound on the maximum squared Hilbert--Schmidt reconstruction error. -/
theorem zorn_cptp_reduced_history_uniform_error (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ))
    (hX : X.sigma_plus i ≠ 0)
    (hUpper : (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef) :
    ∃ W : Flat,
      cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W 0 ≠ 0 ∧
      (∀ Z : Flat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z) = Matrix.trace Z) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (Z : Matrix (r × (Fin 2 × Fin d)) (r × (Fin 2 × Fin d)) ℂ), Z.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
          (InfoGeometry.Modular.Choi.krausChannel
            (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)) Z).PosSemidef) ∧
      (∀ ρ : Flat, ρ.PosSemidef → Matrix.trace ρ = 1 → ∀ k,
        (reducedHistory i X W ρ k).PosSemidef ∧ Matrix.trace (reducedHistory i X W ρ k) = 1) ∧
      ∃ ρ σ : Flat, ρ.PosSemidef ∧ σ.PosSemidef ∧
        Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
        reducedHistory i X W ρ = reducedHistory i X W σ ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ decode : (ℕ → Sheet) → Flat,
          ε ≤ max (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq
              (ρ - decode (reducedHistory i X W ρ)))
            (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq
              (σ - decode (reducedHistory i X W σ))) := by
  have hLower := (matrix_ordered_gram_bounds_iff (X.sigma_plus i)).mp hUpper
  have hBound := zornFlatSlice_bound_of_compressions i X hUpper hLower
  obtain ⟨W, hEven, hResidual⟩ := exists_even_residual zornFlatSheet (zornFlatSlice i X)
    zornFlatSheet_idem hBound
  refine ⟨W, zorn_upper_kraus_ne_zero i X hX W, ?_, ?_, ?_, ?_⟩
  · intro Z
    exact cornerKrausWithResidual_trace _ _ _ Z zornFlatSheet_star hResidual
  · intro r _ _ Z hZ
    exact cornerKrausWithResidual_completely_positive _ _ _ Z hZ
  · intro ρ hPos hTrace k
    exact reducedHistory_is_density i X W ρ hResidual hPos hTrace k
  · obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ := reducedHistory_collision i X W hEven
    refine ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq,
      matrixTraceNormSq (ρ - σ) / 4, ?_, ?_⟩
    · exact div_pos (matrixTraceNormSq_sub_pos hne) (by norm_num)
    · intro decode
      rw [← heq]
      exact two_point_error_lower_bound ρ σ _

/-- For two inputs with the same reduced observation, a rectangular CPTP
replacement channel reaches the exact two-point minimax error. -/
theorem reduced_observation_cptp_minimax (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ)) (W ρ σ : Flat)
    (hResidual : star W * W = 1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X)))
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htρ : Matrix.trace ρ = 1) (htσ : Matrix.trace σ = 1) (k : ℕ)
    (heq : reducedHistory i X W ρ k = reducedHistory i X W σ k) :
    ∃ E : Sheet →ₗ[ℂ] Flat,
      (∀ Y : Sheet, Matrix.trace (E Y) = Matrix.trace Y) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r] (Y : Matrix (r × Fin 2) (r × Fin 2) ℂ),
        Y.PosSemidef → (amplificationTo E Y).PosSemidef) ∧
      max (matrixTraceNormSq (ρ - E (reducedHistory i X W ρ k)))
          (matrixTraceNormSq (σ - E (reducedHistory i X W σ k))) =
        matrixTraceNormSq (ρ - σ) / 4 ∧
      ∀ F : Sheet → Flat,
        matrixTraceNormSq (ρ - σ) / 4 ≤
          max (matrixTraceNormSq (ρ - F (reducedHistory i X W ρ k)))
            (matrixTraceNormSq (σ - F (reducedHistory i X W σ k))) := by
  let M : Flat := (1 / 2 : ℂ) • (ρ + σ)
  have hM := midpoint_is_density ρ σ hρ hσ htρ htσ
  have hOρ := reducedHistory_is_density i X W ρ hResidual hρ htρ k
  have hOσ := reducedHistory_is_density i X W σ hResidual hσ htσ k
  refine ⟨replacementTo M, ?_, ?_, ?_, ?_⟩
  · intro Y
    exact replacementTo_trace M hM.2 Y
  · intro r _ _ Y hY
    exact replacementTo_completely_positive M hM.1 Y hY
  · rw [replacementTo_on_density M _ hOρ.2, replacementTo_on_density M _ hOσ.2]
    rcases midpoint_attains_two_point_bound ρ σ with ⟨hX, hY⟩
    change max (matrixTraceNormSq (ρ - M)) (matrixTraceNormSq (σ - M)) = _
    rw [hX, hY, max_self]
  · intro F
    rw [← heq]
    exact two_point_error_lower_bound ρ σ _

/-- One nontrivial matrix-valued channel and one fixed pair of states have
the same full reduced history. A single CPTP decoder attains the sharp
two-state bound at every time, while no decoder of the complete history
can improve that bound for the pair. -/
theorem zorn_full_history_sharp_cptp_minimax (i : Fin 3)
    (X : OperatorZornMatrix (Matrix (Fin d) (Fin d) ℂ))
    (hX : X.sigma_plus i ≠ 0)
    (hUpper : (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef) :
    ∃ W ρ σ : Flat,
      cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W 0 ≠ 0 ∧
      (∀ Z : Flat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z) = Matrix.trace Z) ∧
      (∀ (r : ℕ) (Z : Matrix (Fin r × (Fin 2 × Fin d))
          (Fin r × (Fin 2 × Fin d)) ℂ), Z.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := Fin r)
          (InfoGeometry.Modular.Choi.krausChannel
            (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)) Z).PosSemidef) ∧
      ρ.PosSemidef ∧ σ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      reducedHistory i X W ρ = reducedHistory i X W σ ∧
      0 < matrixTraceNormSq (ρ - σ) / 4 ∧
      (∀ decode : (ℕ → Sheet) → Flat,
        matrixTraceNormSq (ρ - σ) / 4 ≤
          max (matrixTraceNormSq (ρ - decode (reducedHistory i X W ρ)))
            (matrixTraceNormSq (σ - decode (reducedHistory i X W σ)))) ∧
      ∃ E : Sheet →ₗ[ℂ] Flat,
        (∀ Y : Sheet, Matrix.trace (E Y) = Matrix.trace Y) ∧
        (∀ (r : Type*) [Fintype r] [DecidableEq r] (Y : Matrix (r × Fin 2) (r × Fin 2) ℂ),
          Y.PosSemidef → (amplificationTo E Y).PosSemidef) ∧
        ∀ k, max (matrixTraceNormSq (ρ - E (reducedHistory i X W ρ k)))
            (matrixTraceNormSq (σ - E (reducedHistory i X W σ k))) =
          matrixTraceNormSq (ρ - σ) / 4 := by
  have hLower := (matrix_ordered_gram_bounds_iff (X.sigma_plus i)).mp hUpper
  have hBound := zornFlatSlice_bound_of_compressions i X hUpper hLower
  obtain ⟨W, hEven, hResidual⟩ := exists_even_residual zornFlatSheet (zornFlatSlice i X)
    zornFlatSheet_idem hBound
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ := reducedHistory_collision i X W hEven
  let M : Flat := (1 / 2 : ℂ) • (ρ + σ)
  have hM := midpoint_is_density ρ σ hρ hσ htρ htσ
  refine ⟨W, ρ, σ, zorn_upper_kraus_ne_zero i X hX W, ?_, ?_, hρ, hσ, htρ, htσ, hne, heq,
    div_pos (matrixTraceNormSq_sub_pos hne) (by norm_num), ?_, replacementTo M, ?_, ?_, ?_⟩
  · intro Z
    exact cornerKrausWithResidual_trace _ _ _ Z zornFlatSheet_star hResidual
  · intro r Z hZ
    exact cornerKrausWithResidual_completely_positive _ _ _ Z hZ
  · intro decode
    rw [← heq]
    exact two_point_error_lower_bound ρ σ _
  · intro Y
    exact replacementTo_trace M hM.2 Y
  · intro r _ _ Y hY
    exact replacementTo_completely_positive M hM.1 Y hY
  · intro k
    have hOρ := reducedHistory_is_density i X W ρ hResidual hρ htρ k
    have hOσ := reducedHistory_is_density i X W σ hResidual hσ htσ k
    rw [replacementTo_on_density M _ hOρ.2, replacementTo_on_density M _ hOσ.2]
    rcases midpoint_attains_two_point_bound ρ σ with ⟨hR, hS⟩
    change max (matrixTraceNormSq (ρ - M)) (matrixTraceNormSq (σ - M)) = _
    rw [hR, hS, max_self]

/-- A genuinely noncommuting pair of operator coefficients. -/
def raising : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

def lowering : Matrix (Fin 2) (Fin 2) ℂ := star raising

/-- The two nonzero matrix directions have genuinely noncommuting products. -/
theorem raising_lowering_noncommute : raising * lowering ≠ lowering * raising := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [raising, lowering, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at hentry

def concreteZorn : OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨0, 0, ![0, raising, star raising], fun _ => 0⟩

theorem concreteZorn_noncommuting_and_contractive :
    concreteZorn.sigma_plus 1 ≠ 0 ∧
    concreteZorn.sigma_plus 1 * concreteZorn.sigma_plus 2 ≠
      concreteZorn.sigma_plus 2 * concreteZorn.sigma_plus 1 ∧
    (1 - concreteZorn.sigma_plus 1 * star (concreteZorn.sigma_plus 1)).PosSemidef := by
  have hB : concreteZorn.sigma_plus 1 = raising := by
    simp [concreteZorn]
  have hC : concreteZorn.sigma_plus 2 = star raising := by
    simp [concreteZorn]
  rw [hB, hC]
  have hne : raising ≠ 0 := by
    intro h
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    norm_num [raising] at hentry
  have hnoncomm : raising * star raising ≠ star raising * raising := by
    intro h
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    norm_num [raising, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] at hentry
  refine ⟨hne, hnoncomm, ?_⟩
  have heq : (1 : Matrix (Fin 2) (Fin 2) ℂ) - raising * star raising =
      star raising * raising := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [raising, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply]
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self raising

/-- The full-history recovery bound has a concrete noncommutative matrix
instance, with no assumed existence of a coefficient or of the two states. -/
theorem concreteZorn_uniform_recovery_obstruction :
    ∃ W ρ σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      cornerKrausWithResidual zornFlatSheet (zornFlatSlice 1 concreteZorn) W 0 ≠ 0 ∧
      ρ.PosSemidef ∧ σ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      reducedHistory 1 concreteZorn W ρ = reducedHistory 1 concreteZorn W σ ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∀ decode : (ℕ → Matrix (Fin 2) (Fin 2) ℂ) →
            Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
          ε ≤ max (matrixTraceNormSq (ρ - decode (reducedHistory 1 concreteZorn W ρ)))
            (matrixTraceNormSq (σ - decode (reducedHistory 1 concreteZorn W σ))) := by
  obtain ⟨hX, _, hBound⟩ := concreteZorn_noncommuting_and_contractive
  obtain ⟨W, hK, _, _, _, ρ, σ, hρ, hσ, htρ, htσ, hne, heq, ε, hε, hdecode⟩ :=
    zorn_cptp_reduced_history_uniform_error.{0} 1 concreteZorn hX hBound
  exact ⟨W, ρ, σ, hK, hρ, hσ, htρ, htσ, hne, heq, ε, hε, hdecode⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornHistoryQuantitativeRecovery

end
