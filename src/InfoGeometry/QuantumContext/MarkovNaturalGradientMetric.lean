/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovNaturalGradientSubmersion
import InfoGeometry.QuantumContext.MatrixGNS
import InfoGeometry.QuantumContext.FiniteSoftmaxStationaryGreen

/-!
# Positive definiteness of the full-matrix Markov pairing

The stationary-weighted Frobenius pairing on the entire matrix carrier is a
genuine positive-definite bilinear form when every stationary weight is
strictly positive. Its quadratic form is the diagonal-weight GNS form after
transposing the matrix. This is separate from the Markov Laplacian energy,
which remains semidefinite because it annihilates consensus columns.

For symmetric finite softmax scores, the canonical partition-function
stationary weights supply the required strict positivity and detailed balance,
so the already-defined full-matrix submersion system has a positive-definite
pairing. No gradient inverse or convergence claim is included.
-/

open scoped BigOperators

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
open InfoGeometry.Canonical.NaturalGradientSubmersionFlow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Markov bridge pairing is the GNS quadratic form of the transposed
full matrix for the diagonal weight matrix. All matrix entries participate. -/
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

/-- Under strictly positive weights, the full-matrix quadratic pairing
vanishes only at the zero matrix. -/
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

/-- The full-matrix stationary-weighted pairing is strictly positive on every
nonzero matrix when all weights are strictly positive. -/
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

/-- The full-matrix pairing has zero bilinear radical for strictly positive
weights. -/
theorem weightedMatrixPairing_nondegenerate
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (X : Matrix ι ι ℝ)
    (hX : ∀ Y, weightedMatrixPairing π X Y = 0) : X = 0 := by
  by_contra hne
  have hpos := weightedMatrixPairing_self_pos_of_weights π X hπ hne
  exact (ne_of_gt hpos) (hX X)

/-- The bilinear radical of the full-matrix pairing is trivial exactly on the
zero matrix. -/
theorem weightedMatrixPairing_eq_zero_forall_iff
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (X : Matrix ι ι ℝ) :
    (∀ Y, weightedMatrixPairing π X Y = 0) ↔ X = 0 := by
  constructor
  · exact weightedMatrixPairing_nondegenerate π hπ X
  · rintro rfl Y
    simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn]

/-- The bundled bilinear form is positive definite under pointwise positive
weights. -/
theorem weightedMatrixBilin_self_pos_of_weights
    (π : ι → ℝ) (X : Matrix ι ι ℝ) (hπ : ∀ i, 0 < π i)
    (hX : X ≠ 0) :
    0 < weightedMatrixBilin π X X := by
  change 0 < weightedMatrixPairing π X X
  exact weightedMatrixPairing_self_pos_of_weights π X hπ hX

/-- Specialize positive definiteness to the metric field of the Markov
natural-gradient submersion system. -/
theorem markovNaturalGradientSubmersionSystem_g_pos
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i) (X : Matrix ι ι ℝ) (hX : X ≠ 0) :
    0 < (markovNaturalGradientSubmersionSystem P π hP hDB).g X X := by
  change 0 < weightedMatrixPairing π X X
  exact weightedMatrixPairing_self_pos_of_weights π X hπ hX

variable [Nonempty ι]

/-- Symmetric-score softmax specializes the full-matrix Markov submersion
system to its canonical strictly positive stationary weights. -/
noncomputable def symmetricSoftmaxNaturalGradientSubmersionSystem
    (scores : ι → ι → ℝ) (hsymm : ∀ i j, scores i j = scores j i) :
    NaturalGradientSubmersionSystem (Matrix ι ι ℝ) :=
  markovNaturalGradientSubmersionSystem
    (softmaxAttentionMatrix scores)
    (softmaxPartitionStationaryWeight scores)
    (softmaxAttentionMatrix_mem_rowStochastic scores)
    (softmaxPartitionStationaryWeight_detailedBalance scores hsymm)

/-- The canonical symmetric-softmax submersion system has a positive-definite
pairing on the full matrix carrier. -/
theorem symmetricSoftmaxNaturalGradientSubmersionSystem_g_pos
    (scores : ι → ι → ℝ) (hsymm : ∀ i j, scores i j = scores j i)
    (X : Matrix ι ι ℝ) (hX : X ≠ 0) :
    0 < (symmetricSoftmaxNaturalGradientSubmersionSystem scores hsymm).g X X := by
  change 0 < weightedMatrixPairing
    (softmaxPartitionStationaryWeight scores) X X
  apply weightedMatrixPairing_self_pos_of_weights
  · exact softmaxPartitionStationaryWeight_pos scores
  · exact hX

end InfoGeometry.QuantumContext.MarkovDrazin

end
