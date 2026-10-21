/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-! The quadratic-form readout is a finite sum of squares. -/

theorem gramMatrix_quadratic_eq_sum_sq
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (x : n → ℝ) :
    (∑ i, ∑ j, x i * gramMatrix B i j * x j) =
      ∑ k, (∑ i, x i * B i k) ^ 2 := by
  classical
  calc
    (∑ i, ∑ j, x i * gramMatrix B i j * x j) =
        ∑ i, ∑ j, ∑ k, x i * (B i k * B j k) * x j := by
      simp_rw [gramMatrix_apply, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ k, ∑ j, x i * (B i k * B j k) * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, x i * (B i k * B j k) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ k, (∑ i, x i * B i k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_two, Finset.mul_sum]
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem gramMatrix_quadratic_nonneg
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (x : n → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * gramMatrix B i j * x j := by
  rw [gramMatrix_quadratic_eq_sum_sq B x]
  exact Finset.sum_nonneg (fun k hk => sq_nonneg _)

/-! The quadratic form vanishes on the transpose-side kernel. -/

theorem gramMatrix_quadratic_eq_zero_of_kernel
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (x : n → ℝ)
    (h : ∀ k, ∑ i, x i * B i k = 0) :
    (∑ i, ∑ j, x i * gramMatrix B i j * x j) = 0 := by
  rw [gramMatrix_quadratic_eq_sum_sq B x]
  simp [h]

/-- The Gram quadratic vanishes exactly on the kernel of the transpose map. -/
theorem gramMatrix_quadratic_eq_zero_iff_transpose_mulVec_eq_zero
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (x : n → ℝ) :
    (∑ i, ∑ j, x i * gramMatrix B i j * x j) = 0 ↔
      Bᵀ *ᵥ x = 0 := by
  rw [gramMatrix_quadratic_eq_sum_sq B x]
  have hcolumn (k : m) :
      (Bᵀ *ᵥ x) k = ∑ i, x i * B i k := by
    simp only [Matrix.mulVec, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  constructor
  · intro h
    have hterms : ∀ k : m, (∑ i, x i * B i k) ^ 2 = 0 := by
      intro k
      have hzero :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ)
          (f := fun j => (∑ i, x i * B i j) ^ 2)
          (fun j _ => sq_nonneg _)).mp h
      exact hzero k (Finset.mem_univ k)
    funext k
    rw [hcolumn k]
    exact sq_eq_zero_iff.mp (hterms k)
  · intro h
    apply Finset.sum_eq_zero
    intro k hk
    have hcolumn_zero : ∑ i, x i * B i k = 0 := by
      calc
        ∑ i, x i * B i k = (Bᵀ *ᵥ x) k := (hcolumn k).symm
        _ = 0 := congrFun h k
    simp [hcolumn_zero]

end InfoGeometry.Krein.FiniteGramFactorization
