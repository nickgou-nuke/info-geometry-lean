/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

/-!
# Prototype: a uniform finite-horizon hitting-cost bound

Under a uniform lower bound on one-step transition probability into the target,
the finite Bellman approximants are uniformly bounded by the reciprocal lower
bound. This file is scratch-only and makes no infinite-time or expectation
claim.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovDirichletUniformBoundPrototype

open Matrix
open scoped BigOperators
open InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem row_mass_away_from_target
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (i target : ι) :
    (∑ j ∈ Finset.univ.erase target, P i j) = 1 - P i target := by
  have hsum := Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun j => P i j) (Finset.mem_univ target)
  rw [Matrix.sum_row_of_mem_rowStochastic hP i] at hsum
  linarith

private theorem weighted_sum_away_le
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target i : ι) (ε C : ℝ) (hε : ε ≤ P i target) (hC : 0 ≤ C)
    (f : ι → ℝ) (hf_target : f target = 0)
    (hf_bound : ∀ j, f j ≤ C) :
    (P.mulVec f) i ≤ C * (1 - ε) := by
  have hsum_erase :
      (∑ j, P i j * f j) =
        ∑ j ∈ Finset.univ.erase target, P i j * f j := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun j => P i j * f j) (Finset.mem_univ target)]
    simp [hf_target]
  have hmass := row_mass_away_from_target P hP i target
  calc
    (P.mulVec f) i = ∑ j ∈ Finset.univ.erase target, P i j * f j := by
      rw [Matrix.mulVec, dotProduct, hsum_erase]
    _ ≤ ∑ j ∈ Finset.univ.erase target, P i j * C := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hf_bound j)
        (Matrix.nonneg_of_mem_rowStochastic hP)
    _ = (∑ j ∈ Finset.univ.erase target, P i j) * C := by
      rw [← Finset.sum_mul]
    _ = (1 - P i target) * C := by rw [hmass]
    _ ≤ (1 - ε) * C := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact hC
    _ = C * (1 - ε) := by ring

/-- If every state assigns probability at least `ε` to the target in one step,
then every finite-horizon first-hit Bellman cost is at most `ε⁻¹`. -/
theorem firstHitApproximation_le_inv
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (ε : ℝ) (hε : 0 < ε)
    (hminor : ∀ i, ε ≤ P i target) (n : ℕ) (i : ι) :
    firstHitApproximation P target n i ≤ ε⁻¹ := by
  have hε_le_one : ε ≤ 1 := by
    exact (hminor target).trans (Matrix.le_one_of_mem_rowStochastic hP)
  have hC_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  have hstep : 1 + ε⁻¹ * (1 - ε) = ε⁻¹ := by
    field_simp
    ring
  induction n generalizing i with
  | zero => simp [firstHitApproximation, hC_nonneg]
  | succ n ih =>
      by_cases hi : i = target
      · simp [firstHitApproximation, hi, hC_nonneg]
      · rw [firstHitApproximation_succ_of_ne P target n i hi]
        have hmul := weighted_sum_away_le P hP target i ε ε⁻¹ (hminor i)
          hC_nonneg
          (firstHitApproximation P target n)
          (firstHitApproximation_target P target n)
          (fun j => ih j)
        calc
          1 + (P.mulVec
              (firstHitApproximation P target n)) i
              ≤ 1 + ε⁻¹ * (1 - ε) := by
            simpa [add_comm] using add_le_add_left hmul 1
          _ = ε⁻¹ := hstep

end InfoGeometry.QuantumContext.FiniteMarkovDirichletUniformBoundPrototype
