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


/-- Left telescoping identity; the order of factors is retained. -/
theorem one_sub_mul_finiteGreen (T : R) (N : ℕ) :
    (1 - T) * finiteGreen T N = 1 - T ^ N := by
  induction N with
  | zero => simp [finiteGreen]
  | succ N ih =>
      rw [finiteGreen_succ, mul_add, ih, pow_succ']
      noncomm_ring

/-- Right telescoping identity; no commutative-ring instance is assumed. -/
theorem finiteGreen_mul_one_sub (T : R) (N : ℕ) :
    finiteGreen T N * (1 - T) = 1 - T ^ N := by
  induction N with
  | zero => simp [finiteGreen]
  | succ N ih =>
      rw [finiteGreen_succ, add_mul, ih, pow_succ]
      noncomm_ring

section Ranked

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- A weighted finite graph with a supplied topological ranking. -/
structure RankedKernel (V : Type*) [Fintype V] [DecidableEq V] (R : Type*) [Ring R]
    (N : ℕ) where
  rank : V → Fin N
  weight : Matrix V V R
  strict_support : ∀ i j, (rank i).val ≤ (rank j).val → weight i j = 0

namespace RankedKernel

variable {R : Type*} [Ring R] (K : RankedKernel V R N)

/-- A nonzero length-`k` contribution requires at least `k` rank increases. -/
theorem pow_entry_eq_zero (k : ℕ) (i j : V)
    (h : (K.rank i).val < (K.rank j).val + k) :
    (K.weight ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
      have hij : i ≠ j := by
        intro heq
        subst j
        omega
      simp [hij]
  | succ k ih =>
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _hl
      by_cases hil : (K.rank i).val ≤ (K.rank l).val
      · rw [K.strict_support i l hil, zero_mul]
      · have hlj : (K.rank l).val < (K.rank j).val + k := by omega
        rw [ih l j hlj, mul_zero]

/-- Nilpotence is a consequence of the finite ranking. -/
theorem weight_pow_rank_bound : K.weight ^ N = 0 := by
  ext i j
  apply K.pow_entry_eq_zero
  have hi := (K.rank i).isLt
  omega

/-- The causal Green operator of `1 - weight`. -/
def green : Matrix V V R := finiteGreen K.weight N

/-- The finite path sum is a left inverse of the causal recurrence operator. -/
theorem recurrence_mul_green : (1 - K.weight) * K.green = 1 := by
  rw [green, one_sub_mul_finiteGreen, K.weight_pow_rank_bound, sub_zero]

/-- The same path sum is also a right inverse. -/
theorem green_mul_recurrence : K.green * (1 - K.weight) = 1 := by
  rw [green, finiteGreen_mul_one_sub, K.weight_pow_rank_bound, sub_zero]

/-- The Green operator contains no response to a source of strictly later rank. -/
theorem green_entry_eq_zero_of_rank_lt (i j : V)
    (h : (K.rank i).val < (K.rank j).val) : K.green i j = 0 := by
  change (∑ k ∈ Finset.range N, K.weight ^ k) i j = 0
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro k _hk
  apply K.pow_entry_eq_zero
  omega

/-- The finite inverse solves the inhomogeneous equation exactly. -/
theorem solve (J : Matrix V V R) : (1 - K.weight) * (K.green * J) = J := by
  rw [← mul_assoc, K.recurrence_mul_green, one_mul]

/-- Uniqueness is derived from the proved two-sided inverse. -/
theorem solution_unique (J X : Matrix V V R)
    (hX : (1 - K.weight) * X = J) : X = K.green * J := by
  calc
    X = (K.green * (1 - K.weight)) * X := by
      rw [K.green_mul_recurrence, one_mul]
    _ = K.green * ((1 - K.weight) * X) := mul_assoc _ _ _
    _ = K.green * J := by rw [hX]

end RankedKernel
end Ranked

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

/-- Concrete counterexample to the claim that sixth-power nilpotence forces
the fifth power to be nonzero. -/
theorem sixth_nilpotence_does_not_force_nonzero_fifth_power :
    ∃ T : Matrix (Fin 2) (Fin 2) ℝ,
      T ≠ 0 ∧ T ^ 5 = 0 ∧ T ^ 6 = 0 := by
  refine ⟨twoNodeDAG, twoNodeDAG_ne_zero, ?_, ?_⟩
  · calc
      twoNodeDAG ^ 5 = twoNodeDAG ^ 2 * twoNodeDAG ^ 3 := by rw [← pow_add]
      _ = 0 := by rw [twoNodeDAG_sq, zero_mul]
  · calc
      twoNodeDAG ^ 6 = twoNodeDAG ^ 2 * twoNodeDAG ^ 4 := by rw [← pow_add]
      _ = 0 := by rw [twoNodeDAG_sq, zero_mul]

theorem twoNodeDAG_green_explicit :
    finiteGreen twoNodeDAG 2 = !![1, 0; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteGreen, twoNodeDAG]

/-- The concrete finite Green sum is the two-sided inverse of the edge
operator's complement; the displayed matrix records the actual inverse. -/
theorem twoNodeDAG_green_inverse :
    finiteGreen twoNodeDAG 2 = !![1, 0; 1, 1] ∧
      (1 - twoNodeDAG) * finiteGreen twoNodeDAG 2 = 1 ∧
      finiteGreen twoNodeDAG 2 * (1 - twoNodeDAG) = 1 := by
  refine ⟨twoNodeDAG_green_explicit, ?_, ?_⟩
  · rw [twoNodeDAG_green_explicit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [twoNodeDAG, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [twoNodeDAG_green_explicit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [twoNodeDAG, Matrix.mul_apply, Fin.sum_univ_two]
end
end InfoGeometry.SignedNetwork.RankedDAGResolvent
