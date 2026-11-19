/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.TableBalancing
import Mathlib.Tactic

/-!
# The exact unweighted least-squares projection of a log table

This module uses the finite means and double-centering operator from
InfoGeometry.Spectrometry.TableBalancing. It proves the normal equations rather than assuming
orthogonality, and then proves the full squared-error decomposition, global
minimality, and uniqueness of the fitted additive table.

The row and column factors separately retain the usual additive gauge.
No noise model, statistical weighting, or Sinkhorn optimality is asserted.
-/

namespace InfoGeometry.Spectrometry.LogLeastSquares

open scoped BigOperators
open InfoGeometry.Spectrometry.TableBalancing

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- An arbitrary additive row--column table. -/
def additiveTable (a : I → ℝ) (b : J → ℝ) : I → J → ℝ :=
  fun i j => a i + b j

/-- The finite unweighted additive fit. -/
def additiveFit (L : I → J → ℝ) : I → J → ℝ :=
  fun i j => rowMean L i + colMean L j - grandMean L

def squaredNorm (M : I → J → ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

def squaredError (L F : I → J → ℝ) : ℝ :=
  squaredNorm (fun i j => L i j - F i j)

omit [Nonempty I] [Nonempty J] in
theorem additiveFit_eq_additiveTable (L : I → J → ℝ) :
    additiveFit L =
      additiveTable (rowMean L) (fun j => colMean L j - grandMean L) := by
  funext i j
  unfold additiveFit additiveTable
  ring

omit [Nonempty I] [Nonempty J] in
theorem residual_eq_doubleCenter (L : I → J → ℝ) (i : I) (j : J) :
    L i j - additiveFit L i j = doubleCenter L i j := by
  unfold additiveFit doubleCenter
  ring

omit [Nonempty I] in
theorem sum_row_doubleCenter (L : I → J → ℝ) (i : I) :
    ∑ j, doubleCenter L i j = 0 := by
  have hn : (Fintype.card J : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := rowMean_doubleCenter L i
  simpa only [rowMean, mean, div_eq_zero_iff, hn, or_false] using h

omit [Nonempty J] in
theorem sum_col_doubleCenter (L : I → J → ℝ) (j : J) :
    ∑ i, doubleCenter L i j = 0 := by
  have hn : (Fintype.card I : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := colMean_doubleCenter L j
  simpa only [colMean, mean, div_eq_zero_iff, hn, or_false] using h

/-- The actual double-centered residual is orthogonal to every additive table. -/
theorem interaction_orthogonal_additive (L : I → J → ℝ)
    (a : I → ℝ) (b : J → ℝ) :
    (∑ i, ∑ j, doubleCenter L i j * additiveTable a b i j) = 0 := by
  have hrow : (∑ i, ∑ j, doubleCenter L i j * a i) = 0 := by
    simp only [← Finset.sum_mul, sum_row_doubleCenter, zero_mul,
      Finset.sum_const_zero]
  have hcol : (∑ i, ∑ j, doubleCenter L i j * b j) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, sum_col_doubleCenter, zero_mul,
      Finset.sum_const_zero]
  simp only [additiveTable, mul_add, Finset.sum_add_distrib]
  rw [hrow, hcol, zero_add]

omit [Nonempty I] [Nonempty J] in
theorem squaredNorm_nonneg (M : I → J → ℝ) : 0 ≤ squaredNorm M := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (M i j)

omit [Nonempty I] [Nonempty J] in
theorem squaredNorm_eq_zero_iff (M : I → J → ℝ) :
    squaredNorm M = 0 ↔ ∀ i j, M i j = 0 := by
  constructor
  · intro h i j
    have hi : (∑ k, M i k ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun r _ => Finset.sum_nonneg (fun k _ => sq_nonneg (M r k)))).mp h
          i (Finset.mem_univ i)
    have hij : M i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (M i k))).mp hi
        j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hij
  · intro h
    simp only [squaredNorm, h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]

omit [Nonempty I] [Nonempty J] in
theorem squaredNorm_add (X Y : I → J → ℝ) :
    squaredNorm (fun i j => X i j + Y i j) =
      squaredNorm X + squaredNorm Y + 2 * (∑ i, ∑ j, X i j * Y i j) := by
  have hpoint (i : I) (j : J) :
      (X i j + Y i j) ^ 2 =
        X i j ^ 2 + Y i j ^ 2 + 2 * (X i j * Y i j) := by ring
  unfold squaredNorm
  simp only [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Exact Pythagorean identity for every competing additive row--column table. -/
theorem additive_squared_error_decomposition (L : I → J → ℝ)
    (a : I → ℝ) (b : J → ℝ) :
    squaredError L (additiveTable a b) =
      squaredNorm (doubleCenter L) +
        squaredError (additiveFit L) (additiveTable a b) := by
  have hsplit :
      (fun i j => L i j - additiveTable a b i j) =
        (fun i j => doubleCenter L i j +
          (additiveFit L i j - additiveTable a b i j)) := by
    funext i j
    unfold additiveFit doubleCenter
    ring
  have hdiff :
      (fun i j => additiveFit L i j - additiveTable a b i j) =
        additiveTable (fun i => rowMean L i - a i)
          (fun j => colMean L j - grandMean L - b j) := by
    funext i j
    unfold additiveFit additiveTable
    ring
  have horth :
      (∑ i, ∑ j, doubleCenter L i j *
        (additiveFit L i j - additiveTable a b i j)) = 0 := by
    have hpoint (i : I) (j : J) := congrFun (congrFun hdiff i) j
    simp_rw [hpoint]
    exact interaction_orthogonal_additive L _ _
  unfold squaredError
  rw [hsplit, squaredNorm_add, horth, mul_zero, add_zero]

omit [Nonempty I] [Nonempty J] in
theorem additiveFit_error_eq_interaction (L : I → J → ℝ) :
    squaredError L (additiveFit L) = squaredNorm (doubleCenter L) := by
  unfold squaredError
  congr 1
  funext i j
  exact residual_eq_doubleCenter L i j

/-- Global optimality over every additive table, without statistical assumptions. -/
theorem additiveFit_minimizes (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) :
    squaredError L (additiveFit L) ≤ squaredError L (additiveTable a b) := by
  rw [additiveFit_error_eq_interaction, additive_squared_error_decomposition]
  exact le_add_of_nonneg_right
    (squaredNorm_nonneg (fun i j => additiveFit L i j - additiveTable a b i j))

/-- The optimal fitted table is unique, although its row/column factors are not. -/
theorem additiveFit_unique (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) :
    squaredError L (additiveTable a b) = squaredError L (additiveFit L) ↔
      additiveTable a b = additiveFit L := by
  constructor
  · intro h
    have hzero : squaredError (additiveFit L) (additiveTable a b) = 0 := by
      rw [additive_squared_error_decomposition, additiveFit_error_eq_interaction] at h
      linarith
    have hpoint := (squaredNorm_eq_zero_iff
      (fun i j => additiveFit L i j - additiveTable a b i j)).mp hzero
    funext i j
    have hij := hpoint i j
    linarith
  · intro h
    rw [h]

end
end InfoGeometry.Spectrometry.LogLeastSquares
