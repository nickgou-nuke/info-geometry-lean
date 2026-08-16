import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Finite Gram factorization readout

This owner records the elementary finite backbone behind coincidence models:
an amplitude matrix `B` produces the Gram matrix `B Bᵀ`.  The statements are
coordinate-level and deliberately do not claim complete positivity, NMF
existence, factor uniqueness, or a matrix-order PSD API.
-/

open Matrix

namespace InfoGeometry.Krein.FiniteGramFactorization

def gramMatrix {n m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) : Matrix n n ℝ :=
  B * B.transpose

theorem gramMatrix_apply {n m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (i j : n) :
    gramMatrix B i j = ∑ k, B i k * B j k := by
  simp [gramMatrix, Matrix.mul_apply, Matrix.transpose_apply]

theorem gramMatrix_symmetric {n m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) :
    (gramMatrix B).transpose = gramMatrix B := by
  ext i j
  change gramMatrix B j i = gramMatrix B i j
  rw [gramMatrix_apply, gramMatrix_apply]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem gramMatrix_diag_nonneg {n m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (i : n) :
    0 ≤ gramMatrix B i i := by
  rw [gramMatrix_apply]
  exact Finset.sum_nonneg (fun k hk => mul_self_nonneg (B i k))

theorem gramMatrix_entry_nonneg
    {n m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ)
    (hB : ∀ i k, 0 ≤ B i k) (i j : n) :
    0 ≤ gramMatrix B i j := by
  rw [gramMatrix_apply]
  exact Finset.sum_nonneg (fun k hk => mul_nonneg (hB i k) (hB j k))

end InfoGeometry.Krein.FiniteGramFactorization
