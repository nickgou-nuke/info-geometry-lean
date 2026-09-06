import Mathlib.LinearAlgebra.Matrix.Diagonal
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

end InfoGeometry.Probability
