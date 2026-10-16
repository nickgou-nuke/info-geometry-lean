/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMetriplecticFlowBridge
import InfoGeometry.QuantumContext.MatrixGNS

/-!
# Strict positivity of the full-matrix stationary-weighted pairing

This scratch result uses the repository-owned `weightedMatrixPairing` on the
entire matrix carrier. It proves strict positivity on nonzero matrices when
every stationary weight is positive, and derives nondegeneracy from that
quadratic positivity.
-/

open scoped BigOperators

namespace InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Markov bridge pairing is the GNS quadratic form of the transposed
full matrix for the diagonal weight matrix. This is an equality on the whole
matrix carrier, not a diagonal restriction. -/
theorem weightedMatrixPairing_eq_gnsInner_transpose
    (π : ι → ℝ) (X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X X =
      InfoGeometry.QuantumContext.MatrixGNS.gnsInner
        (Matrix.diagonal π) X.transpose X.transpose := by
  rw [InfoGeometry.QuantumContext.MatrixGNS.gnsInner_self_diagonal]
  unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pow_two]
  exact mul_assoc (π i) (X i j) (X i j)

/-- The zero set of the full-matrix quadratic pairing is exactly the zero
matrix, by transport to the existing faithful diagonal GNS form. -/
theorem weightedMatrixPairing_self_eq_zero_iff
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (X : Matrix ι ι ℝ) :
    weightedMatrixPairing π X X = 0 ↔ X = 0 := by
  rw [weightedMatrixPairing_eq_gnsInner_transpose]
  change InfoGeometry.QuantumContext.MatrixGNS.gnsLeftIdeal
    (Matrix.diagonal π) X.transpose ↔ X = 0
  rw [InfoGeometry.QuantumContext.MatrixGNS.gnsLeftIdeal_faithful π hπ]
  constructor
  · intro h
    have ht : X.transpose = 0 := h
    have := congrArg Matrix.transpose ht
    simpa using this
  · intro h
    rw [h]
    ext i j
    simp [Matrix.transpose_apply]

/-- The existing full-matrix weighted pairing is strictly positive on every
nonzero matrix when all row weights are strictly positive. -/
theorem weightedMatrixPairing_self_pos_of_weights
    (π : ι → ℝ) (X : Matrix ι ι ℝ) (hπ : ∀ i, 0 < π i)
    (hX : X ≠ 0) :
    0 < weightedMatrixPairing π X X := by
  have hnonneg : 0 ≤ weightedMatrixPairing π X X := by
    rw [weightedMatrixPairing_eq_gnsInner_transpose]
    exact InfoGeometry.QuantumContext.MatrixGNS.gnsInner_self_nonneg π
      (fun i => (hπ i).le) X.transpose
  have hne : weightedMatrixPairing π X X ≠ 0 := by
    intro hz
    exact hX ((weightedMatrixPairing_self_eq_zero_iff π hπ X).mp hz)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The full-matrix pairing is nondegenerate: if a matrix pairs to zero against
every matrix, it must itself be zero. This follows by testing against itself
and using strict positivity, not by restricting to a diagonal subspace. -/
theorem weightedMatrixPairing_nondegenerate
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (X : Matrix ι ι ℝ)
    (hX : ∀ Y, weightedMatrixPairing π X Y = 0) : X = 0 := by
  by_contra hne
  have hpos := weightedMatrixPairing_self_pos_of_weights π X hπ hne
  have hzero := hX X
  exact (ne_of_gt hpos) hzero

/-- Quadratic positivity and nondegeneracy give the exact zero-detection
equivalence for this full-matrix pairing. -/
theorem weightedMatrixPairing_eq_zero_forall_iff
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (X : Matrix ι ι ℝ) :
    (∀ Y, weightedMatrixPairing π X Y = 0) ↔ X = 0 := by
  constructor
  · exact weightedMatrixPairing_nondegenerate π hπ X
  · rintro rfl Y
    simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn]

end InfoGeometry.QuantumContext.MarkovDrazin
