/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import InfoGeometry.Probability.FiniteMarkovWeightedAdjoint

/-!
# Finite reversible Markov Dirichlet energy

This module proves the finite weighted edge-energy identity from row
stochasticity and the repository's detailed-balance predicate. It makes no
claim that the pairing is positive definite or that its nullspace consists
only of constants.
-/

open scoped BigOperators

namespace InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite stationary-weighted bilinear pairing on observables. -/
def weightedMarkovPairing (π x y : ι → ℝ) : ℝ :=
  ∑ i, π i * x i * y i

/-- Reversible Markov Dirichlet identity.

The right side is the edge-energy convention with a factor `1/2`, counting
both orientations of each reversible edge. -/
theorem weightedMarkovPairing_laplacian_eq_half_edge_energy
    (P : Matrix ι ι ℝ) (π x : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P) :
    weightedMarkovPairing π x (x - Matrix.mulVec P x) =
      (1 / 2 : ℝ) * ∑ i, ∑ j,
        π i * P i j * (x i - x j) ^ 2 := by
  classical
  have hrow (i : ι) : ∑ j, P i j = 1 :=
    Matrix.sum_row_of_mem_rowStochastic hP i
  have hdb (i j : ι) : π i * P i j = π j * P j i := by
    have hcurrent :=
      (InfoGeometry.Probability.detailedBalance_iff_all_edge_currents_zero π P).mp hDB i j
    dsimp [InfoGeometry.Probability.stationaryEdgeCurrent] at hcurrent
    exact sub_eq_zero.mp hcurrent
  have hfirst :
      (∑ i, ∑ j, π i * P i j * (x i) ^ 2) =
        ∑ i, π i * (x i) ^ 2 := by
    calc
      (∑ i, ∑ j, π i * P i j * (x i) ^ 2) =
          ∑ i, π i * (x i) ^ 2 * (∑ j, P i j) := by
            congr 1
            funext i
            calc
              (∑ j, π i * P i j * (x i) ^ 2) =
                  ∑ j, (π i * (x i) ^ 2) * P i j := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = (π i * (x i) ^ 2) * ∑ j, P i j := by
                    rw [Finset.mul_sum]
      _ = ∑ i, π i * (x i) ^ 2 := by simp [hrow]
  have hsecond :
      (∑ i, ∑ j, π i * P i j * (x j) ^ 2) =
        ∑ i, π i * (x i) ^ 2 := by
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, π i * P i j * (x j) ^ 2) =
          ∑ j, (x j) ^ 2 * (∑ i, π j * P j i) := by
            congr 1
            funext j
            calc
              (∑ i, π i * P i j * (x j) ^ 2) =
                  ∑ i, (x j) ^ 2 * (π j * P j i) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [hdb i j]
                    ring
              _ = (x j) ^ 2 * ∑ i, π j * P j i := by
                    rw [Finset.mul_sum]
      _ = ∑ j, π j * (x j) ^ 2 := by
            congr 1
            funext j
            rw [← Finset.mul_sum, hrow j]
            ring
      _ = ∑ i, π i * (x i) ^ 2 := by rfl
  have hcross :
      (∑ i, ∑ j, π i * P i j * (x i * x j)) =
        ∑ i, π i * x i * (Matrix.mulVec P x) i := by
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_left_comm, mul_comm]
  unfold weightedMarkovPairing
  simp only [Pi.sub_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [show (∑ i, π i * x i * (x i - ∑ j, P i j * x j)) =
      (∑ i, π i * (x i) ^ 2) -
        (∑ i, π i * x i * (Matrix.mulVec P x) i) by
        simp [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib,
          mul_sub, mul_assoc, mul_left_comm, mul_comm, sq]]
  rw [show (∑ i, ∑ j,
      π i * P i j * (x i - x j) ^ 2) =
      (∑ i, ∑ j,
        ((π i * P i j * (x i) ^ 2) +
          (π i * P i j * (x j) ^ 2) -
          2 * (π i * P i j * (x i * x j)))) by
        congr 1
        funext i
        congr 1
        funext j
        ring]
  rw [← hcross]
  rw [← hfirst]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hfirst_second :
      (∑ i, ∑ j, π i * P i j * (x i) ^ 2) =
        (∑ i, ∑ j, π i * P i j * (x j) ^ 2) := hfirst.trans hsecond.symm
  simp_rw [← Finset.mul_sum]
  linear_combination (1 / 2 : ℝ) * hfirst_second

/-- Nonnegativity of the reversible Dirichlet form for nonnegative weights.
This is a semidefinite statement only; no nullspace characterization is
asserted. -/
theorem weightedMarkovPairing_laplacian_nonneg
    (P : Matrix ι ι ℝ) (π x : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 ≤ π i) :
    0 ≤ weightedMarkovPairing π x (x - Matrix.mulVec P x) := by
  rw [weightedMarkovPairing_laplacian_eq_half_edge_energy P π x hP hDB]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg
  · exact mul_nonneg (hπ i) (Matrix.nonneg_of_mem_rowStochastic hP)
  · exact sq_nonneg _

/-- Detailed balance makes the transition part symmetric for the
stationary-weighted bilinear pairing. This is a finite algebraic identity; it
does not assert that the pairing is nondegenerate or positive. -/
theorem weightedMarkovPairing_mulVec_symmetric
    (P : Matrix ι ι ℝ) (π x y : ι → ℝ)
    (hDB : InfoGeometry.Probability.DetailedBalance π P) :
    weightedMarkovPairing π x (Matrix.mulVec P y) =
      weightedMarkovPairing π (Matrix.mulVec P x) y := by
  classical
  have hdb (i j : ι) : π i * P i j = π j * P j i := by
    have hcurrent :=
      (InfoGeometry.Probability.detailedBalance_iff_all_edge_currents_zero π P).mp hDB i j
    dsimp [InfoGeometry.Probability.stationaryEdgeCurrent] at hcurrent
    exact sub_eq_zero.mp hcurrent
  unfold weightedMarkovPairing
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  calc
    (∑ i, ∑ j, π i * x i * (P i j * y j)) =
        ∑ i, ∑ j, π i * P i j * x i * y j := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ac_rfl
    _ = ∑ i, ∑ j, π j * P j i * x i * y j := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [hdb i j]
    _ = ∑ i, ∑ j, π i * P i j * x j * y i := by
          rw [Finset.sum_comm]
    _ = ∑ i, (∑ j, π i * (P i j * x j)) * y i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ac_rfl

/-- The difference operator `I - P` is symmetric for the stationary-weighted
bilinear pairing whenever `P` satisfies detailed balance. -/
theorem weightedMarkovPairing_laplacian_symmetric
    (P : Matrix ι ι ℝ) (π x y : ι → ℝ)
    (hDB : InfoGeometry.Probability.DetailedBalance π P) :
    weightedMarkovPairing π x (y - Matrix.mulVec P y) =
      weightedMarkovPairing π (x - Matrix.mulVec P x) y := by
  calc
    weightedMarkovPairing π x (y - Matrix.mulVec P y) =
        weightedMarkovPairing π x y -
          weightedMarkovPairing π x (Matrix.mulVec P y) := by
            simp [weightedMarkovPairing, Pi.sub_apply, mul_sub,
              Finset.sum_sub_distrib]
    _ = weightedMarkovPairing π x y -
          weightedMarkovPairing π (Matrix.mulVec P x) y := by
            rw [weightedMarkovPairing_mulVec_symmetric P π x y hDB]
    _ = weightedMarkovPairing π (x - Matrix.mulVec P x) y := by
            unfold weightedMarkovPairing
            calc
              (∑ i, (π i * x i) * y i) -
                  ∑ i, (π i * Matrix.mulVec P x i) * y i =
                  ∑ i, ((π i * x i) * y i -
                    (π i * Matrix.mulVec P x i) * y i) := by
                      rw [Finset.sum_sub_distrib]
              _ = ∑ i, (π i * x i -
                    π i * Matrix.mulVec P x i) * y i := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [sub_mul]
              _ = ∑ i, π i * (x - Matrix.mulVec P x) i * y i := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      simp only [Pi.sub_apply]
                      rw [mul_sub]

/-- Under strictly positive reversible weights and transitions, the Dirichlet
energy vanishes exactly on constant observables. This statement supplies the
support hypothesis that is absent from the general semidefinite result. -/
theorem weightedMarkovPairing_laplacian_eq_zero_iff_const
    [Nonempty ι] (P : Matrix ι ι ℝ) (π x : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i) (hPpos : ∀ i j, 0 < P i j) :
    weightedMarkovPairing π x (x - Matrix.mulVec P x) = 0 ↔
      ∃ c : ℝ, ∀ i, x i = c := by
  rw [weightedMarkovPairing_laplacian_eq_half_edge_energy P π x hP hDB]
  constructor
  · intro henergy
    have hsum : (∑ i, ∑ j, π i * P i j * (x i - x j) ^ 2) = 0 := by
      have hmul : (1 / 2 : ℝ) *
          (∑ i, ∑ j, π i * P i j * (x i - x j) ^ 2) = 0 := henergy
      exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨x i₀, fun i => ?_⟩
    have hterm_nonneg (i j : ι) :
        0 ≤ π i * P i j * (x i - x j) ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt (hπ i))
        (le_of_lt (hPpos i j))) (sq_nonneg _)
    have hrow_nonneg (i : ι) :
        0 ≤ ∑ j, π i * P i j * (x i - x j) ^ 2 :=
      Finset.sum_nonneg fun j _ => hterm_nonneg i j
    have hinner_le (i j : ι) :
        π i * P i j * (x i - x j) ^ 2 ≤
          ∑ k, π i * P i k * (x i - x k) ^ 2 :=
      Finset.single_le_sum (fun k _ => hterm_nonneg i k)
        (Finset.mem_univ j)
    have houter_le (i : ι) :
        (∑ j, π i * P i j * (x i - x j) ^ 2) ≤
          ∑ k, ∑ j, π k * P k j * (x k - x j) ^ 2 :=
      Finset.single_le_sum (fun k _ => hrow_nonneg k)
        (Finset.mem_univ i)
    have hterm_zero (i j : ι) :
        π i * P i j * (x i - x j) ^ 2 = 0 := by
      apply le_antisymm
      · have hle := (hinner_le i j).trans (houter_le i)
        simpa [hsum] using hle
      · exact hterm_nonneg i j
    have heq (j : ι) : x i₀ = x j := by
      by_contra hne
      have hsq : 0 < (x i₀ - x j) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
      have hpos : 0 < π i₀ * P i₀ j * (x i₀ - x j) ^ 2 :=
        mul_pos (mul_pos (hπ i₀) (hPpos i₀ j)) hsq
      rw [hterm_zero i₀ j] at hpos
      exact (lt_irrefl 0) hpos
    exact heq i |>.symm
  · rintro ⟨c, hc⟩
    have hsum : (∑ i, ∑ j, π i * P i j * (x i - x j) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      simp [hc]
    rw [hsum]
    simp

end InfoGeometry.QuantumContext.MarkovDrazin
