/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.FiniteMarkovWeightedAdjoint
import Mathlib.Tactic

/-!
# Detailed balance and a lower-triangular finite kernel

This module proves a conditional finite-matrix obstruction. A lower-triangular
matrix with row sums one that satisfies detailed balance for a strictly positive
weight is the identity. It does not identify masked transformer weights with a
Markov kernel; row sums and detailed balance remain explicit inputs.
-/

namespace InfoGeometry.Probability

/-- Detailed balance and causal triangular support force every off-diagonal
entry to vanish when the reference weights are strictly positive. Here
`i < j → P i j = 0` is the lower-triangular support convention. -/
theorem causal_detailedBalance_offDiagonal_zero
    {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i, 0 < π i)
    (hcausal : ∀ i j, i < j → P i j = 0)
    (hbalance : DetailedBalance π P) :
    ∀ i j, i ≠ j → P i j = 0 := by
  have hcurrent := (detailedBalance_iff_all_edge_currents_zero π P).mp hbalance
  intro i j hij
  rcases lt_trichotomy i j with hij' | hij' | hji'
  · exact hcausal i j hij'
  · exact (hij hij').elim
  · have hji_zero : P j i = 0 := hcausal j i hji'
    have hbal := hcurrent j i
    dsimp [stationaryEdgeCurrent] at hbal
    rw [hji_zero, mul_zero, zero_sub] at hbal
    have hprod : π i * P i j = 0 := by linarith
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (hπ i))

/-- A lower-triangular matrix with row sums one and positive-weight detailed
balance is the identity matrix. Entrywise nonnegativity is not needed for this
implication (and follows from the conclusion). -/
theorem causal_detailedBalance_rowSumOne_eq_one
    {n : ℕ} (π : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hπ : ∀ i, 0 < π i)
    (hcausal : ∀ i j, i < j → P i j = 0)
    (hbalance : DetailedBalance π P)
    (hrow : ∀ i, ∑ j, P i j = 1) :
    P = 1 := by
  have hoff := causal_detailedBalance_offDiagonal_zero π P hπ hcausal hbalance
  have hsum (i : Fin n) : (∑ j, P i j) = P i i := by
    classical
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hji
      exact hoff i j hji.symm
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hdiag (i : Fin n) : P i i = 1 := by
    have h := hrow i
    rw [hsum i] at h
    exact h
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hdiag]
  · simp [hij, hoff i j hij]

end InfoGeometry.Probability
