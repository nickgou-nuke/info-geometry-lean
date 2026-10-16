/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Finite-horizon Dirichlet cost approximants

For a finite row-stochastic transition matrix and a target state, these
approximants start at zero and apply the finite-horizon first-hit Bellman
update. They satisfy the target boundary condition, are monotone in the
horizon, and are bounded above by the horizon. This file proves those finite
algebraic facts only; it does not identify the sequence's order-colimit with a
probabilistic expectation.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bellman iterates for the first-hit cost truncated at a finite horizon. -/
def firstHitApproximation (P : Matrix ι ι ℝ) (target : ι) : ℕ → (ι → ℝ)
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      if i = target then 0 else 1 + (P.mulVec (firstHitApproximation P target n)) i

theorem firstHitApproximation_target (P : Matrix ι ι ℝ) (target : ι) (n : ℕ) :
    firstHitApproximation P target n target = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [firstHitApproximation]

theorem firstHitApproximation_succ_of_ne (P : Matrix ι ι ℝ) (target : ι)
    (n : ℕ) (i : ι) (hi : i ≠ target) :
    firstHitApproximation P target (n + 1) i =
      1 + (P.mulVec (firstHitApproximation P target n)) i := by
  simp [firstHitApproximation, hi]

omit [DecidableEq ι] in
private theorem mulVec_nonneg_of_entries_nonneg
    (P : Matrix ι ι ℝ) (x : ι → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hx : ∀ j, 0 ≤ x j) (i : ι) :
    0 ≤ (P.mulVec x) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hP i j) (hx j)

omit [DecidableEq ι] in
private theorem mulVec_mono_of_entries_nonneg
    (P : Matrix ι ι ℝ) (x y : ι → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hxy : ∀ j, x j ≤ y j) (i : ι) :
    (P.mulVec x) i ≤ (P.mulVec y) i := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (hP i j)

/-- Nonnegativity of every finite-horizon cost iterate. -/
theorem firstHitApproximation_nonneg
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (n : ℕ) (i : ι) :
    0 ≤ firstHitApproximation P target n i := by
  induction n generalizing i with
  | zero => simp [firstHitApproximation]
  | succ n ih =>
      by_cases hi : i = target
      · simp [firstHitApproximation, hi]
      · rw [firstHitApproximation_succ_of_ne P target n i hi]
        have hmul : 0 ≤ (P.mulVec (firstHitApproximation P target n)) i :=
          mulVec_nonneg_of_entries_nonneg P _
            (fun i j => Matrix.nonneg_of_mem_rowStochastic hP)
            (fun j => ih j) i
        exact add_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hmul

/-- Increasing the horizon cannot decrease the truncated first-hit cost. -/
theorem firstHitApproximation_mono
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (n : ℕ) (i : ι) :
    firstHitApproximation P target n i ≤
      firstHitApproximation P target (n + 1) i := by
  induction n generalizing i with
  | zero =>
      by_cases hi : i = target
      · simp [firstHitApproximation, hi]
      · simp [firstHitApproximation, hi, Matrix.mulVec, dotProduct]
  | succ n ih =>
      by_cases hi : i = target
      · simp [firstHitApproximation, hi]
      · rw [firstHitApproximation_succ_of_ne P target n i hi,
          firstHitApproximation_succ_of_ne P target (n + 1) i hi]
        have hmono := mulVec_mono_of_entries_nonneg P
            (firstHitApproximation P target n)
            (firstHitApproximation P target (n + 1))
            (fun i j => Matrix.nonneg_of_mem_rowStochastic hP) (fun j => ih j) i
        exact add_le_add (le_refl 1) hmono

/-- The truncated cost is at most the number of available steps. -/
theorem firstHitApproximation_le_horizon
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (n : ℕ) (i : ι) :
    firstHitApproximation P target n i ≤ n := by
  induction n generalizing i with
  | zero => simp [firstHitApproximation]
  | succ n ih =>
      by_cases hi : i = target
      · simp [firstHitApproximation, hi]
        exact_mod_cast Nat.zero_le (n + 1)
      · rw [firstHitApproximation_succ_of_ne P target n i hi]
        have hweighted :
            (P.mulVec (firstHitApproximation P target n)) i ≤ n := by
          calc
            (P.mulVec (firstHitApproximation P target n)) i =
                ∑ j, P i j * firstHitApproximation P target n j := by
                  simp [Matrix.mulVec, dotProduct]
            _ ≤ ∑ j, P i j * (n : ℝ) := by
                  apply Finset.sum_le_sum
                  intro j _
                  exact mul_le_mul_of_nonneg_left (ih j)
                    (Matrix.nonneg_of_mem_rowStochastic hP)
            _ = n := by
                  rw [← Finset.sum_mul]
                  rw [Matrix.sum_row_of_mem_rowStochastic hP i]
                  simp
        rw [Nat.cast_succ]
        have htotal : (1 : ℝ) +
            (P.mulVec (firstHitApproximation P target n)) i ≤
              1 + (n : ℝ) :=
          add_le_add (le_refl (1 : ℝ)) hweighted
        simpa [add_comm] using htotal

private theorem row_mass_away_from_target
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (i target : ι) :
    (∑ j ∈ Finset.univ.erase target, P i j) = 1 - P i target := by
  have hsum := Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun j => P i j) (Finset.mem_univ target)
  rw [Matrix.sum_row_of_mem_rowStochastic hP i] at hsum
  linarith

private theorem scale_by_complementary_mass_le
    (ε a C : ℝ) (hε : ε ≤ a) (hC : 0 ≤ C) :
    (1 - a) * C ≤ C * (1 - ε) := by
  have hcoeff : 1 - a ≤ 1 - ε := sub_le_sub_left hε 1
  calc
    (1 - a) * C ≤ (1 - ε) * C :=
      mul_le_mul_of_nonneg_right hcoeff hC
    _ = C * (1 - ε) := mul_comm _ _

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
    _ ≤ C * (1 - ε) := scale_by_complementary_mass_le ε (P i target) C hε hC

/-- A uniform lower bound on the one-step transition probability into the
target bounds every finite-horizon first-hit cost by its reciprocal. This
gives the boundedness needed for the order-colimit owner. -/
theorem firstHitApproximation_le_inv_of_target_minorization
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (target : ι) (ε : ℝ) (hε : 0 < ε)
    (hminor : ∀ i, ε ≤ P i target) (n : ℕ) (i : ι) :
    firstHitApproximation P target n i ≤ ε⁻¹ := by
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

end InfoGeometry.QuantumContext.FiniteMarkovDirichletApproximation
