/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Bipartite marginal pushforward and log-interaction

Tri-factor marginalization is linear and needs column sums, not positivity.
Probability claims additionally need nonnegativity and unit latent mass.
The log-interaction is invariant under positive row/column scaling. The row
and column terms are geometric/logarithmic effects, not arithmetic marginals.
This file does not claim Sinkhorn convergence, uniqueness of a copula, an
NMF optimizer, or nonzero interaction merely from having two mixture terms.
-/
noncomputable section
namespace InfoGeometry.Probability.BipartiteLogCoupling
open scoped BigOperators
variable {I J K L : Type*}
variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

/-- Native rectangular matrix multiplication supplies the response map. -/
theorem triFactor_row_marginal
    (U : Matrix I K ℝ) (S : Matrix K L ℝ) (V : Matrix J L ℝ)
    (hV : ∀ l, ∑ j, V j l = 1) :
    (U * S * V.transpose).mulVec 1 = U.mulVec (S.mulVec 1) := by
  have hv : V.transpose.mulVec 1 = 1 := by
    funext l
    simpa [Matrix.mulVec, dotProduct] using hV l
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv]

/-- Column marginalization is the transposed row identity. -/
theorem triFactor_col_marginal
    (U : Matrix I K ℝ) (S : Matrix K L ℝ) (V : Matrix J L ℝ)
    (hU : ∀ k, ∑ i, U i k = 1) :
    (U * S * V.transpose).transpose.mulVec 1 = V.mulVec (S.transpose.mulVec 1) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc]
  exact triFactor_row_marginal V S.transpose U hU

theorem triFactor_total_mass
    (U : Matrix I K ℝ) (S : Matrix K L ℝ) (V : Matrix J L ℝ)
    (hU : ∀ k, ∑ i, U i k = 1) (hV : ∀ l, ∑ j, V j l = 1) :
    (∑ i, ∑ j, (U * S * V.transpose) i j) = ∑ k, ∑ l, S k l := by
  have hr (i : I) : (∑ j, (U * S * V.transpose) i j) =
      ∑ k, U i k * (∑ l, S k l) := by
    simpa [Matrix.mulVec, dotProduct] using congrFun (triFactor_row_marginal U S V hV) i
  simp_rw [hr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul, hU k, one_mul]

theorem diagonal_core_is_peak_sum
    (U : Matrix I K ℝ) (w : K → ℝ) (V : Matrix J K ℝ) (i : I) (j : J) :
    (U * Matrix.diagonal w * V.transpose) i j = ∑ k, w k * (U i k * V j k) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

def average (I : Type*) [Fintype I] : Matrix I I ℝ :=
  fun _ _ => (Fintype.card I : ℝ)⁻¹

def center (I : Type*) [Fintype I] [DecidableEq I] : Matrix I I ℝ :=
  1 - average I

def interaction (X : Matrix I J ℝ) : Matrix I J ℝ := center I * X * center J

def rowShift (u : I → ℝ) : Matrix I J ℝ := fun i _ => u i

def colShift (v : J → ℝ) : Matrix I J ℝ := fun _ j => v j

lemma average_transpose : (average I).transpose = average I := rfl
lemma center_transpose : (center I).transpose = center I := by
  simp [center, Matrix.transpose_sub, average_transpose]

lemma average_idempotent [Nonempty I] : average I * average I = average I := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext i j
  simp only [Matrix.mul_apply, average, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

lemma complementary_average [Nonempty I] :
    average I * center I = 0 ∧ center I * average I = 0 ∧ center I * center I = center I := by
  have hh := average_idempotent (I := I)
  constructor
  · rw [center, mul_sub, mul_one, hh, sub_self]
  constructor
  · rw [center, sub_mul, one_mul, hh, sub_self]
  · dsimp only [center]
    noncomm_ring [hh]

/-- Complete four-term reconstruction in rectangular matrix space. -/
theorem four_term_split (X : Matrix I J ℝ) :
    average I * X * average J + center I * X * average J +
      average I * X * center J + center I * X * center J = X := by
  have hI : average I + center I = 1 := by simp [center]
  have hJ : average J + center J = 1 := by simp [center]
  calc
    _ = (average I + center I) * X * (average J + center J) := by
      simp only [Matrix.add_mul, Matrix.mul_add]
      abel
    _ = X := by rw [hI, hJ, Matrix.one_mul, Matrix.mul_one]

lemma frobenius_left_zero (P Q : Matrix I I ℝ) (h : P.transpose * Q = 0)
    (B C : Matrix J J ℝ) (X Y : Matrix I J ℝ) :
    Matrix.trace ((P * X * B).transpose * (Q * Y * C)) = 0 := by
  have he : (P * X * B).transpose * (Q * Y * C) =
      B.transpose * X.transpose * (P.transpose * Q) * Y * C := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [he, h, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]

lemma frobenius_right_zero (P Q : Matrix I I ℝ) (B C : Matrix J J ℝ)
    (h : C * B.transpose = 0) (X Y : Matrix I J ℝ) :
    Matrix.trace ((P * X * B).transpose * (Q * Y * C)) = 0 := by
  rw [Matrix.trace_mul_comm]
  have he : (Q * Y * C) * (P * X * B).transpose =
      Q * Y * (C * B.transpose) * X.transpose * P.transpose := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [he, h, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]

/-- All six distinct component pairs, not just four of the six. -/
theorem six_orthogonal_pairs [Nonempty I] [Nonempty J] (X : Matrix I J ℝ) :
    let G := average I * X * average J
    let R := center I * X * average J
    let C := average I * X * center J
    let T := interaction X
    Matrix.trace (G.transpose * R) = 0 ∧
    Matrix.trace (G.transpose * C) = 0 ∧
    Matrix.trace (G.transpose * T) = 0 ∧
    Matrix.trace (R.transpose * C) = 0 ∧
    Matrix.trace (R.transpose * T) = 0 ∧
    Matrix.trace (C.transpose * T) = 0 := by
  dsimp only [interaction]
  have hI := complementary_average (I := I)
  have hJ := complementary_average (I := J)
  have hi : (average I).transpose * center I = 0 := by rw [average_transpose]; exact hI.1
  have hi' : (center I).transpose * average I = 0 := by rw [center_transpose]; exact hI.2.1
  have hj : center J * (average J).transpose = 0 := by rw [average_transpose]; exact hJ.2.1
  exact ⟨frobenius_left_zero _ _ hi _ _ X X,
    frobenius_right_zero _ _ _ _ hj X X,
    frobenius_left_zero _ _ hi _ _ X X,
    frobenius_left_zero _ _ hi' _ _ X X,
    frobenius_right_zero _ _ _ _ hj X X,
    frobenius_left_zero _ _ hi _ _ X X⟩

lemma rowShift_center [Nonempty J] (u : I → ℝ) :
    (rowShift u : Matrix I J ℝ) * center J = 0 := by
  have hn : (Fintype.card J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h : (rowShift u : Matrix I J ℝ) * average J = rowShift u := by
    ext i j
    simp only [Matrix.mul_apply, average, rowShift, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp [hn]
    <;> ring
  rw [center, Matrix.mul_sub, Matrix.mul_one, h, sub_self]

lemma center_colShift [Nonempty I] (v : J → ℝ) :
    center I * (colShift v : Matrix I J ℝ) = 0 := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h : average I * (colShift v : Matrix I J ℝ) = colShift v := by
    ext i j
    simp only [Matrix.mul_apply, average, colShift, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [center, Matrix.sub_mul, Matrix.one_mul, h, sub_self]

/-- Additive marginal changes are annihilated exactly. -/
theorem interaction_shift [Nonempty I] [Nonempty J]
    (X : Matrix I J ℝ) (u : I → ℝ) (v : J → ℝ) :
    interaction (X + rowShift u + colShift v) = interaction X := by
  have hr : center I * rowShift u * center J = 0 := by
    rw [Matrix.mul_assoc, rowShift_center, Matrix.mul_zero]
  have hc : center I * colShift v * center J = 0 := by
    rw [center_colShift, Matrix.zero_mul]
  simp only [interaction, Matrix.mul_add, Matrix.add_mul, hr, hc, add_zero]

/-- Logarithms are entrywise, and positivity is explicit. -/
theorem log_scaling_invariant [Nonempty I] [Nonempty J]
    (P : Matrix I J ℝ) (a : I → ℝ) (b : J → ℝ)
    (hp : ∀ i j, 0 < P i j) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    interaction (fun i j => Real.log (a i * P i j * b j)) =
      interaction (fun i j => Real.log (P i j)) := by
  have he : (fun i j => Real.log (a i * P i j * b j)) =
      (fun i j => Real.log (P i j)) + rowShift (fun i => Real.log (a i)) +
        colShift (fun j => Real.log (b j)) := by
    ext i j
    rw [Real.log_mul (ne_of_gt (mul_pos (ha i) (hp i j))) (ne_of_gt (hb j)),
      Real.log_mul (ne_of_gt (ha i)) (ne_of_gt (hp i j))]
    simp only [Matrix.add_apply, rowShift, colShift]
    ring
  rw [he, interaction_shift]

theorem log_product_zero [Nonempty I] [Nonempty J]
    (a : I → ℝ) (b : J → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    interaction (fun i j => Real.log (a i * b j)) = 0 := by
  have h := interaction_shift (0 : Matrix I J ℝ)
    (fun i => Real.log (a i)) (fun j => Real.log (b j))
  have he : (fun i j => Real.log (a i * b j)) =
      (0 : Matrix I J ℝ) + rowShift (fun i => Real.log (a i)) +
        colShift (fun j => Real.log (b j)) := by
    ext i j
    simp [rowShift, colShift, Real.log_mul (ne_of_gt (ha i)) (ne_of_gt (hb j))]
  rw [he, h]
  simp [interaction]

/-- Exact two-peak dependence: the 2-by-2 minor factorizes. -/
theorem two_peak_minor (w u₁ u₂ a₁ a₂ v₁ v₂ b₁ b₂ : ℝ) :
    (w * u₁ * v₁ + (1-w) * a₁ * b₁) * (w * u₂ * v₂ + (1-w) * a₂ * b₂) -
      (w * u₁ * v₂ + (1-w) * a₁ * b₂) * (w * u₂ * v₁ + (1-w) * a₂ * b₁) =
      w * (1-w) * (u₁ * a₂ - a₁ * u₂) * (v₁ * b₂ - b₁ * v₂) := by
  ring

/-- Two distinct positive product components can still have zero interaction. -/
theorem distinct_two_peak_zero_interaction :
    let a : Fin 2 → ℝ := ![1/4, 3/4]
    let c : Fin 2 → ℝ := ![3/4, 1/4]
    let b : Fin 2 → ℝ := ![1/3, 2/3]
    a ≠ c ∧
    (∀ i j, 0 < a i * b j ∧ 0 < c i * b j) ∧
    interaction (fun i j => Real.log ((1/2) * (a i * b j) + (1/2) * (c i * b j))) = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hh := congrFun h 0
    norm_num at hh
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  · have he : (fun i j : Fin 2 => (1/2 : ℝ) * (![1/4, 3/4] i * ![1/3, 2/3] j) +
        (1/2) * (![3/4, 1/4] i * ![1/3, 2/3] j)) =
        fun i j => (1/2 : ℝ) * ![1/3, 2/3] j := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    change interaction ((fun i j => Real.log ((fun i j : Fin 2 =>
      (1/2 : ℝ) * (![1/4, 3/4] i * ![1/3, 2/3] j) +
      (1/2) * (![3/4, 1/4] i * ![1/3, 2/3] j)) i j))) = 0
    rw [he]
    apply log_product_zero
    · intro i; norm_num
    · intro j; fin_cases j <;> norm_num

end InfoGeometry.Probability.BipartiteLogCoupling
