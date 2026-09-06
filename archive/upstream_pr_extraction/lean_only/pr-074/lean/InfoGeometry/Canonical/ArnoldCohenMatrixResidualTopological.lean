import Mathlib

/-!
# Matrix residual for the Arnold--Cohen regularizer

This file formalizes the finite matrix polynomial appearing in the proposed
regularizer.  Its `W_ij` are rank-two skew matrix readouts and the residual
uses ordinary matrix multiplication.  This is deliberately not identified
with the exterior-algebra Arnold relation or with flatness of a connection.
-/

namespace InfoGeometry.Canonical

open scoped BigOperators

abbrev BasisMatrix (dIn dE : ℕ) := Matrix (Fin dIn) (Fin dE) ℝ

def basisBivector {dIn dE : ℕ}
    (Γ : BasisMatrix dIn dE) (i j : Fin dIn) :
    Matrix (Fin dE) (Fin dE) ℝ :=
  fun p q => Γ i p * Γ j q - Γ j p * Γ i q

def matrixProduct {dE : ℕ}
    (A B : Matrix (Fin dE) (Fin dE) ℝ) :
    Matrix (Fin dE) (Fin dE) ℝ :=
  fun p q => ∑ r : Fin dE, A p r * B r q

def arnoldCohenMatrixResidual {dIn dE : ℕ}
    (Γ : BasisMatrix dIn dE) (i j k : Fin dIn) :
    Matrix (Fin dE) (Fin dE) ℝ :=
  matrixProduct (basisBivector Γ i j) (basisBivector Γ j k) +
    matrixProduct (basisBivector Γ j k) (basisBivector Γ k i) +
    matrixProduct (basisBivector Γ k i) (basisBivector Γ i j)

def arnoldCohenFrobeniusLoss {dIn dE : ℕ}
    (Γ : BasisMatrix dIn dE) (i j k : Fin dIn) : ℝ :=
  ∑ p : Fin dE, ∑ q : Fin dE,
    (arnoldCohenMatrixResidual Γ i j k p q) ^ 2

theorem basisBivector_self {dIn dE : ℕ}
    (Γ : BasisMatrix dIn dE) (i : Fin dIn) :
    basisBivector Γ i i = 0 := by
  ext p q
  simp [basisBivector]

theorem basisBivector_swap {dIn dE : ℕ}
    (Γ : BasisMatrix dIn dE) (i j : Fin dIn) :
    basisBivector Γ j i = -(basisBivector Γ i j) := by
  ext p q
  simp [basisBivector]

theorem continuous_arnoldCohenMatrixResidual {dIn dE : ℕ}
    (i j k : Fin dIn) (p q : Fin dE) :
    Continuous (fun Γ : BasisMatrix dIn dE =>
      arnoldCohenMatrixResidual Γ i j k p q) := by
  unfold arnoldCohenMatrixResidual matrixProduct basisBivector
  fun_prop

theorem continuous_arnoldCohenFrobeniusLoss {dIn dE : ℕ}
    (i j k : Fin dIn) :
    Continuous (fun Γ : BasisMatrix dIn dE =>
      arnoldCohenFrobeniusLoss Γ i j k) := by
  unfold arnoldCohenFrobeniusLoss
  apply continuous_finset_sum
  intro p hp
  apply continuous_finset_sum
  intro q hq
  exact (continuous_arnoldCohenMatrixResidual i j k p q).pow 2

theorem arnoldCohenFrobeniusLoss_nonneg {dIn dE : ℕ}
    (Γ : BasisMatrix dIn dE) (i j k : Fin dIn) :
    0 ≤ arnoldCohenFrobeniusLoss Γ i j k := by
  unfold arnoldCohenFrobeniusLoss
  exact Finset.sum_nonneg (fun p hp =>
    Finset.sum_nonneg (fun q hq => sq_nonneg _))

def arnoldCohenZeroLocus {dIn dE : ℕ} (i j k : Fin dIn) :
    Set (BasisMatrix dIn dE) :=
  {Γ | arnoldCohenFrobeniusLoss Γ i j k = 0}

theorem arnoldCohenZeroLocus_isClosed {dIn dE : ℕ}
    (i j k : Fin dIn) :
    IsClosed (arnoldCohenZeroLocus (dE := dE) i j k) := by
  change IsClosed
    ((fun Γ : BasisMatrix dIn dE =>
      arnoldCohenFrobeniusLoss Γ i j k) ⁻¹' ({0} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_arnoldCohenFrobeniusLoss i j k)

theorem arnoldCohenMatrixResidual_eq_zero_of_rows_equal
    {dIn dE : ℕ} (Γ : BasisMatrix dIn dE) (i j k : Fin dIn)
    (hrows : ∀ a b : Fin dIn, ∀ p : Fin dE, Γ a p = Γ b p) :
    arnoldCohenMatrixResidual Γ i j k = 0 := by
  unfold arnoldCohenMatrixResidual
  have hij : basisBivector Γ i j = 0 := by
    ext p q
    dsimp [basisBivector]
    rw [hrows i j p, hrows i j q]
    ring
  have hjk : basisBivector Γ j k = 0 := by
    ext p q
    dsimp [basisBivector]
    rw [hrows j k p, hrows j k q]
    ring
  have hki : basisBivector Γ k i = 0 := by
    ext p q
    dsimp [basisBivector]
    rw [hrows k i p, hrows k i q]
    ring
  rw [hij, hjk, hki]
  ext p q
  simp [matrixProduct]

end InfoGeometry.Canonical
