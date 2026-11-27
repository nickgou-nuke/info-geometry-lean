/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.QuantumDataProcessingInequality
import InfoGeometry.QuantumContext.MarkovObliqueSupportWitness

/-!
# A complex complete-positivity obstruction for the Markov range compression

The full matrix compression `X ↦ E * X * E`, for the concrete two-state
Markov group-inverse range idempotent `E`, is not completely positive under
the repository's finite-amplification definition. The witness remains on the
noncommutative `2 × 2` matrix carrier; no diagonal or scalar replacement is
used.
-/

namespace InfoGeometry.QuantumContext.MarkovCompressionNotCompletelyPositive

open InfoGeometry.Modular.QuantumDPI
open InfoGeometry.QuantumContext.MarkovObliqueSupportWitness

private noncomputable def complexRangeIdempotent : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (rangeIdempotent i j : ℂ)

private noncomputable def markovCompression :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := complexRangeIdempotent * X * complexRangeIdempotent
  map_add' X Y := by simp only [mul_add, add_mul]
  map_smul' c X := by
    simp only [RingHom.id_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_mul_assoc, mul_smul_comm]

private def witnessVector : Fin 2 → ℂ :=
  fun i => if i = 0 then 1 else Complex.I

private theorem complexRangeIdempotent_not_posSemidef :
    ¬ IsPosSemidef complexRangeIdempotent := by
  intro h
  have him := (h witnessVector).2
  dsimp [complexRangeIdempotent, rangeIdempotent] at him
  rw [rangeIdempotent_eq] at him
  norm_num [witnessVector, Fin.sum_univ_two] at him

private def unitAmplificationInput :
    Matrix (Fin 2 × PUnit) (Fin 2 × PUnit) ℂ := 1

private theorem unitAmplificationInput_pos :
    IsPosSemidef unitAmplificationInput := by
  intro v
  have hterm : ∀ x : Fin 2 × PUnit,
      0 ≤ (starRingEnd ℂ (v x) * v x).re ∧ (starRingEnd ℂ (v x) * v x).im = 0 := by
    intro x
    rw [← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_nonneg]
  have hsum : ∑ i : Fin 2 × PUnit, ∑ j : Fin 2 × PUnit,
      starRingEnd ℂ (v i) * unitAmplificationInput i j * v j =
      ∑ i : Fin 2 × PUnit, starRingEnd ℂ (v i) * v i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [unitAmplificationInput, Matrix.one_apply]
  rw [hsum]
  constructor
  · rw [Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => (hterm i).1
  · rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun i _ => (hterm i).2

private theorem unitAmplification_output_eq_compression_one :
    amplifyMap markovCompression unitAmplificationInput =
      fun ⟨i, _⟩ ⟨j, _⟩ => markovCompression 1 i j := by
  ext ⟨i, a⟩ ⟨j, b⟩
  cases a
  cases b
  have harg : (fun r s : Fin 2 => unitAmplificationInput (r, PUnit.unit) (s, PUnit.unit)) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [unitAmplificationInput, Matrix.one_apply]
  dsimp [amplifyMap]
  rw [harg]

/-- The concrete complexification of the Markov range compression is not CP
under the repository's complete-positivity predicate. -/
theorem markovCompression_not_completelyPositive :
    ¬ IsCompletelyPositive markovCompression := by
  intro hCP
  have hOutput := hCP PUnit unitAmplificationInput unitAmplificationInput_pos
  rw [unitAmplification_output_eq_compression_one] at hOutput
  have hIdemReal : rangeIdempotent * rangeIdempotent = rangeIdempotent :=
    markovRangeIdempotent_idempotent transition laplacianGroupInverse
      laplacianGroupInverse_isGroupInverse
  have hIdem : complexRangeIdempotent * complexRangeIdempotent =
      complexRangeIdempotent := by
    ext i j
    have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => (M i j : ℂ)) hIdemReal
    simpa [complexRangeIdempotent, Matrix.mul_apply] using hij
  have hCompression : markovCompression 1 = complexRangeIdempotent := by
    simp [markovCompression, Matrix.mul_one, hIdem]
  apply complexRangeIdempotent_not_posSemidef
  intro v
  have h := hOutput (fun ⟨i, _⟩ => v i)
  have hsum : (∑ x : Fin 2 × PUnit, ∑ y : Fin 2 × PUnit,
      starRingEnd ℂ (v x.1) * (fun ⟨i, _⟩ ⟨j, _⟩ => markovCompression 1 i j) x y * v y.1) =
      ∑ i : Fin 2, ∑ j : Fin 2, starRingEnd ℂ (v i) * complexRangeIdempotent i j * v j := by
    simp [Fintype.sum_prod_type, hCompression]
  rw [hsum] at h
  exact h

/-- Typed existential witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem markovCompression_mat2c_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.QuantumContext.MarkovCompressionNotCompletelyPositive
