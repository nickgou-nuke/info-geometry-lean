/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Diagonal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

noncomputable section

/-!
# Finite stationary-weighted balance

This file records the finite algebraic core of detailed balance.  It does not
identify an arbitrary connectivity matrix with a Markov generator and does
not assert an entropy-production theorem without rate/support hypotheses.
-/

namespace InfoGeometry.Probability

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal matrix of a finite stationary weight. -/
def stationaryWeightMatrix (π : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal π

/-- Weighted detailed-balance residual for a generator-like matrix. -/
def detailedBalanceResidual (π : n → ℝ) (L : Matrix n n ℝ) : Matrix n n ℝ :=
  stationaryWeightMatrix π * L - L.transpose * stationaryWeightMatrix π

theorem detailedBalanceResidual_transpose
    (π : n → ℝ) (L : Matrix n n ℝ) :
    (detailedBalanceResidual π L).transpose =
      -(detailedBalanceResidual π L) := by
  simp [detailedBalanceResidual, stationaryWeightMatrix,
    Matrix.transpose_mul, sub_eq_add_neg, smul_add, smul_neg]

/-- Detailed balance relative to the stationary weight. -/
def DetailedBalance (π : n → ℝ) (L : Matrix n n ℝ) : Prop :=
  detailedBalanceResidual π L = 0

/-- The stationary edge current associated with a weighted generator entry. -/
def stationaryEdgeCurrent
    (π : n → ℝ) (L : Matrix n n ℝ) (i j : n) : ℝ :=
  π i * L i j - π j * L j i

theorem detailedBalanceResidual_apply
    (π : n → ℝ) (L : Matrix n n ℝ) (i j : n) :
    detailedBalanceResidual π L i j =
      stationaryEdgeCurrent π L i j := by
  simp [detailedBalanceResidual, stationaryWeightMatrix,
    stationaryEdgeCurrent, sub_eq_add_neg]
  ring

theorem detailedBalance_iff_all_edge_currents_zero
    (π : n → ℝ) (L : Matrix n n ℝ) :
    DetailedBalance π L ↔
      ∀ i j, stationaryEdgeCurrent π L i j = 0 := by
  constructor
  · intro h i j
    have hij := congr_fun (congr_fun h i) j
    have hji := congr_fun (congr_fun h j) i
    simp [detailedBalanceResidual, stationaryWeightMatrix,
      stationaryEdgeCurrent] at hij hji ⊢
    linarith
  · intro h
    ext i j
    simp [detailedBalanceResidual, stationaryWeightMatrix,
      stationaryEdgeCurrent] at h ⊢
    simpa [mul_comm] using h i j

theorem stationaryEdgeCurrent_swap
    (π : n → ℝ) (L : Matrix n n ℝ) (i j : n) :
    stationaryEdgeCurrent π L j i =
      -stationaryEdgeCurrent π L i j := by
  simp [stationaryEdgeCurrent, sub_eq_add_neg, add_comm]

/-- The adjoint relative to the diagonal weight matrix. -/
noncomputable def weightedAdjoint
    (π : n → ℝ) (L : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => (π i)⁻¹ * L j i * π j

omit [DecidableEq n] in
/-- The weighted adjoint reverses the order of matrix multiplication. -/
theorem weightedAdjoint_mul
    (π : n → ℝ) (A B : Matrix n n ℝ) (hπ : ∀ i, π i ≠ 0) :
    weightedAdjoint π (A * B) = weightedAdjoint π B * weightedAdjoint π A := by
  classical
  ext i j
  simp only [weightedAdjoint, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  field_simp [hπ i, hπ k]

omit [Fintype n] in
/-- The weighted adjoint fixes the identity matrix. -/
theorem weightedAdjoint_one (π : n → ℝ) (hπ : ∀ i, π i ≠ 0) :
    weightedAdjoint π (1 : Matrix n n ℝ) = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [weightedAdjoint, hπ i]
  · have hji : j ≠ i := Ne.symm hij
    simp [weightedAdjoint, hij, hji]

omit [Fintype n] [DecidableEq n] in
/-- The weighted adjoint preserves matrix subtraction. -/
theorem weightedAdjoint_sub (π : n → ℝ) (A B : Matrix n n ℝ) :
    weightedAdjoint π (A - B) = weightedAdjoint π A - weightedAdjoint π B := by
  ext i j
  simp only [weightedAdjoint, Matrix.sub_apply]
  ring_nf

/-- Detailed balance is self-adjointness for the weighted adjoint. -/
theorem detailedBalance_iff_weightedAdjoint_eq
    (π : n → ℝ) (L : Matrix n n ℝ)
    (hπ : ∀ i, π i ≠ 0) :
    DetailedBalance π L ↔ weightedAdjoint π L = L := by
  constructor
  · intro h
    ext i j
    have hij := detailedBalance_iff_all_edge_currents_zero π L |>.mp h i j
    have hbal : L j i * π j = π i * L i j := by
      have hEq : π i * L i j = π j * L j i := by
        exact sub_eq_zero.mp (by simpa [stationaryEdgeCurrent] using hij)
      calc
        L j i * π j = π j * L j i := by ring
        _ = π i * L i j := hEq.symm
    simp [weightedAdjoint] at ⊢
    calc
      (π i)⁻¹ * L j i * π j = (π i)⁻¹ * (L j i * π j) := by ring
      _ = (π i)⁻¹ * (π i * L i j) := by rw [hbal]
      _ = L i j := by field_simp [hπ i]
  · intro h
    apply detailedBalance_iff_all_edge_currents_zero π L |>.mpr
    intro i j
    have hij := congr_fun (congr_fun h i) j
    simp [weightedAdjoint] at hij
    field_simp [hπ i] at hij
    dsimp [stationaryEdgeCurrent]
    have : π i * L i j = π j * L j i := by
      nlinarith [hij]
    linarith

def stationaryWhitening (π : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (π i))

def stationaryWhiteningInv (π : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (π i))⁻¹)

def whitenedGenerator (π : n → ℝ) (L : Matrix n n ℝ) : Matrix n n ℝ :=
  stationaryWhitening π * L * stationaryWhiteningInv π

theorem detailedBalance_iff_whitened_symmetric
    (π : n → ℝ) (L : Matrix n n ℝ) (hπ : ∀ i, 0 < π i) :
    DetailedBalance π L ↔
      (whitenedGenerator π L).transpose = whitenedGenerator π L := by
  constructor
  · intro h
    ext i j
    have hbal := congr_fun (congr_fun h i) j
    simp [whitenedGenerator, stationaryWhitening,
      stationaryWhiteningInv, detailedBalanceResidual,
      stationaryWeightMatrix, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.diagonal] at hbal ⊢
    have hsi : Real.sqrt (π i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hπ i))
    have hsj : Real.sqrt (π j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hπ j))
    field_simp [hsi, hsj]
    rw [Real.sq_sqrt (le_of_lt (hπ i)),
      Real.sq_sqrt (le_of_lt (hπ j))]
    linarith [hbal]
  · intro h
    ext i j
    have hsym := congr_fun (congr_fun h i) j
    simp [whitenedGenerator, stationaryWhitening,
      stationaryWhiteningInv, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.diagonal] at hsym
    have hsi : Real.sqrt (π i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hπ i))
    have hsj : Real.sqrt (π j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hπ j))
    field_simp [hsi, hsj] at hsym
    have hbal : π i * L i j = π j * L j i := by
      rw [Real.sq_sqrt (le_of_lt (hπ i)),
        Real.sq_sqrt (le_of_lt (hπ j))] at hsym
      exact hsym.symm
    rw [detailedBalanceResidual_apply]
    simp [stationaryEdgeCurrent]
    linarith [hbal]

/-! ### Single-space rigidity: symmetric + causal forces DIAGONAL, not identity

The often-repeated claim that a self-adjoint causal (lower-triangular) matrix
must be the identity is **false**. Symmetry transports the vanishing above the
diagonal to vanishing below it, so such a matrix is diagonal; the identity needs
an additional normalization. For example, unit row sums suffice, as shown by
`causalSymmetric_rowSumOne_eq_one` below. These lemmas make the corrected form
kernel-checked so it can be cited. -/

section SingleSpaceRigidity

variable [LinearOrder n]

/-- `P` is causal lower-triangular: entries strictly above the diagonal vanish. -/
def IsCausalLowerTriangular (P : Matrix n n ℝ) : Prop := ∀ i j, i < j → P i j = 0

/-- `P` is symmetric. -/
def IsSymmetricMatrix (P : Matrix n n ℝ) : Prop := ∀ i j, P i j = P j i

omit [Fintype n] [DecidableEq n] in
/-- **Single-space rigidity, stated correctly.**
A matrix that is both symmetric and causal lower-triangular is *diagonal*.

This is the correct form of "self-adjoint causal implies identity". The identity
does **not** follow; see `causalSymmetric_forcesIdentity_false`. -/
theorem symmetric_causalTriangular_isDiagonal (P : Matrix n n ℝ)
    (hs : IsSymmetricMatrix P) (hc : IsCausalLowerTriangular P) (i j : n) (hij : i ≠ j) :
    P i j = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact hc i j h
  · rw [hs i j, hc j i h]

/-- A symmetric causal matrix is therefore also *upper*-triangular: its strictly
lower-triangular entries vanish. -/
theorem symmetric_causalTriangular_isUpper (P : Matrix n n ℝ)
    (hs : IsSymmetricMatrix P) (hc : IsCausalLowerTriangular P) (i j : n) (hji : j < i) :
    P i j = 0 :=
  symmetric_causalTriangular_isDiagonal P hs hc i j (ne_of_gt hji)

/-- **Detailed balance plus causality forces DIAGONAL, not the identity.**

This is the exact form of the claim that `π`-weighted self-adjointness
(`π i * P i j = π j * P j i`, i.e. `DetailedBalance π P`) collapses a causal
lower-triangular generator to `1`. It collapses to *diagonal*. Row sums equal to
`1` are what would force the identity, and even then only via
`causalSymmetric_rowSumOne_eq_one` in the unweighted case.

Proof: causality kills `P i j` for `i < j`; for `j < i` it kills `P j i`, and
detailed balance transports that vanishing to `P i j` because `π i ≠ 0`. -/
theorem detailedBalance_causalTriangular_isDiagonal (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, π i ≠ 0)
    (hdb : DetailedBalance π P) (hc : IsCausalLowerTriangular P)
    (i j : n) (hij : i ≠ j) : P i j = 0 := by
  have hcur : ∀ i j, stationaryEdgeCurrent π P i j = 0 :=
    (detailedBalance_iff_all_edge_currents_zero π P).mp hdb
  rcases lt_or_gt_of_ne hij with h | h
  · exact hc i j h
  · have hj : P j i = 0 := hc j i h
    have h0 : π i * P i j = 0 := by
      simpa [stationaryEdgeCurrent, hj] using hcur i j
    exact (mul_eq_zero.mp h0).resolve_left (hπ i)

/-- **The identity is recovered once unit row sums are imposed.**
A symmetric causal matrix whose row sums are all `1` is the identity: it is
diagonal, and row `i` then reads `P i i = ∑ j, P i j = 1`.

Nonnegativity is *not* needed — diagonal plus unit row sums already forces the
identity — so it is deliberately not a hypothesis here. -/
theorem causalSymmetric_rowSumOne_eq_one (P : Matrix n n ℝ)
    (hs : IsSymmetricMatrix P) (hc : IsCausalLowerTriangular P)
    (hrow : ∀ i, ∑ j, P i j = 1) (i j : n) :
    P i j = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    have hsum := hrow i
    have hsingle : (∑ k, P i k) = P i i := by
      calc (∑ k, P i k) = ∑ k, if k = i then P i k else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : k = i
            · simp [hk]
            · rw [symmetric_causalTriangular_isDiagonal P hs hc i k (Ne.symm hk), if_neg hk]
        _ = P i i := by simp
    rw [← hsingle, hsum]
    simp
  · rw [symmetric_causalTriangular_isDiagonal P hs hc i j hij, if_neg hij]

end SingleSpaceRigidity

section Counterexample

/-- A symmetric, causal, diagonal matrix that is **not** the identity. -/
def diagSignNeOne : Matrix (Fin 2) (Fin 2) ℝ := !![(-1 : ℝ), 0; 0, 1]

theorem diagSignNeOne_isSymmetric : IsSymmetricMatrix diagSignNeOne := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagSignNeOne, IsSymmetricMatrix]

theorem diagSignNeOne_isCausal : IsCausalLowerTriangular diagSignNeOne := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [diagSignNeOne] at hij ⊢ <;> omega

theorem diagSignNeOne_ne_one : diagSignNeOne ≠ 1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M (0 : Fin 2) (0 : Fin 2)) h
  norm_num [diagSignNeOne] at h00

/-- **Self-adjointness plus causality does not force the identity.**
There is a symmetric causal matrix on a single positively-weighted sheet that
differs from `1`, so the "unique structure" reading of a causal self-adjoint
operator is false without an extra normalization hypothesis. -/
theorem causalSymmetric_forcesIdentity_false :
    ¬ (∀ P : Matrix (Fin 2) (Fin 2) ℝ,
        IsSymmetricMatrix P → IsCausalLowerTriangular P → P = 1) := by
  intro h
  exact absurd (h diagSignNeOne diagSignNeOne_isSymmetric diagSignNeOne_isCausal)
    diagSignNeOne_ne_one

end Counterexample

end InfoGeometry.Probability
