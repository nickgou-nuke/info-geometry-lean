/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
namespace InfoGeometry.SignedNetwork.RankedDAGResolvent
noncomputable section
variable {R : Type*} [Ring R]
def finiteGreen (T : R) (N : ℕ) : R := ∑ k ∈ Finset.range N, T^k
theorem finiteGreen_zero (T : R) : finiteGreen T 0 = 0 := by simp [finiteGreen]
theorem finiteGreen_succ (T : R) (N : ℕ) : finiteGreen T (N+1) = finiteGreen T N + T^N := by simp [finiteGreen, Finset.sum_range_succ]
theorem finiteGreen_left_inverse (T : R) (N : ℕ) (hT : T^N = 0) : (1-T) * finiteGreen T N = 1 := by
  unfold finiteGreen
  calc
    (1 - T) * (∑ k ∈ Finset.range N, T ^ k) =
        -((T - 1) * (∑ k ∈ Finset.range N, T ^ k)) := by noncomm_ring
    _ = -(T ^ N - 1) := by rw [mul_geom_sum]
    _ = 1 := by simp [hT]
theorem finiteGreen_right_inverse (T : R) (N : ℕ) (hT : T^N = 0) : finiteGreen T N * (1-T) = 1 := by
  unfold finiteGreen
  calc
    (∑ k ∈ Finset.range N, T ^ k) * (1 - T) =
        -((∑ k ∈ Finset.range N, T ^ k) * (T - 1)) := by noncomm_ring
    _ = -(T ^ N - 1) := by rw [geom_sum_mul]
    _ = 1 := by simp [hT]

def twoNodeDAG : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

theorem twoNodeDAG_sq : twoNodeDAG ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoNodeDAG, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The concrete edge operator is nonzero, despite being nilpotent. -/
theorem twoNodeDAG_ne_zero : twoNodeDAG ≠ 0 := by
  intro h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) h
  norm_num [twoNodeDAG] at h10

/-- A nilpotent commit-transfer operator need not have nilpotence index six:
this nonzero two-node DAG operator already has square zero, hence also fifth
and sixth powers zero. -/
theorem twoNodeDAG_fifth_and_sixth_powers_zero :
    twoNodeDAG ^ 5 = 0 ∧ twoNodeDAG ^ 6 = 0 := by
  constructor
  · calc
      twoNodeDAG ^ 5 = twoNodeDAG ^ 2 * twoNodeDAG ^ 3 := by
        rw [← pow_add]
      _ = 0 := by rw [twoNodeDAG_sq, zero_mul]
  · calc
      twoNodeDAG ^ 6 = twoNodeDAG ^ 2 * twoNodeDAG ^ 4 := by
        rw [← pow_add]
      _ = 0 := by rw [twoNodeDAG_sq, zero_mul]

/-- Concrete counterexample to the claim that sixth-power nilpotence forces
the fifth power to be nonzero. -/
theorem sixth_nilpotence_does_not_force_nonzero_fifth_power :
    ∃ T : Matrix (Fin 2) (Fin 2) ℝ,
      T ≠ 0 ∧ T ^ 5 = 0 ∧ T ^ 6 = 0 := by
  exact ⟨twoNodeDAG, twoNodeDAG_ne_zero,
    twoNodeDAG_fifth_and_sixth_powers_zero.1,
    twoNodeDAG_fifth_and_sixth_powers_zero.2⟩

theorem twoNodeDAG_green_left :
    (1 - twoNodeDAG) * finiteGreen twoNodeDAG 2 = 1 := by
  exact finiteGreen_left_inverse twoNodeDAG 2 twoNodeDAG_sq

theorem twoNodeDAG_green_right :
    finiteGreen twoNodeDAG 2 * (1 - twoNodeDAG) = 1 := by
  exact finiteGreen_right_inverse twoNodeDAG 2 twoNodeDAG_sq

theorem twoNodeDAG_green_explicit :
    finiteGreen twoNodeDAG 2 = !![1, 0; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteGreen, twoNodeDAG]
end
end InfoGeometry.SignedNetwork.RankedDAGResolvent
