/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
import Mathlib.Tactic

/-!
# Algebraic laws of the finite supertrace

Linearity of the parity supertrace and its commutator/anticommutator identities.
These are transported from the pre-integration stash snapshot; the base owner
continues to hold the operator-level definitions and their gate-cleared proofs.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParitySupertraceAlgebra

open InfoGeometry.OperatorAlgebra.FiniteParitySupertrace

variable {n : Type*} [Fintype n] [DecidableEq n]


theorem supertrace_add (sign : n → ℝ) (A B : Matrix n n ℝ) :
    supertrace sign (A + B) = supertrace sign A + supertrace sign B := by
  rw [supertrace_eq_sum_sign_mul_diagonal,
    supertrace_eq_sum_sign_mul_diagonal,
    supertrace_eq_sum_sign_mul_diagonal]
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]


theorem supertrace_smul (sign : n → ℝ) (c : ℝ) (A : Matrix n n ℝ) :
    supertrace sign (c • A) = c * supertrace sign A := by
  rw [supertrace_eq_sum_sign_mul_diagonal,
    supertrace_eq_sum_sign_mul_diagonal]
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    ∑ i, sign i * (c * A i i) = ∑ i, c * (sign i * A i i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring_nf
    _ = c * ∑ i, sign i * A i i := by
      rw [Finset.mul_sum]


theorem supertrace_neg (sign : n → ℝ) (A : Matrix n n ℝ) :
    supertrace sign (-A) = -supertrace sign A := by
  rw [supertrace_eq_sum_sign_mul_diagonal,
    supertrace_eq_sum_sign_mul_diagonal]
  simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]


theorem supertrace_sub (sign : n → ℝ) (A B : Matrix n n ℝ) :
    supertrace sign (A - B) = supertrace sign A - supertrace sign B := by
  rw [sub_eq_add_neg, supertrace_add, supertrace_neg]
  rfl


theorem supertrace_mul_comm_of_even_right
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hB : IsEven sign B) :
    supertrace sign (A * B) = supertrace sign (B * A) := by
  exact (supertrace_mul_comm_of_even_left sign B A hB).symm


theorem supertrace_mul_comm_of_odd_right
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hB : IsOdd sign B) :
    supertrace sign (A * B) = -supertrace sign (B * A) := by
  have h := supertrace_mul_comm_of_odd_left sign B A hB
  rw [h]
  simp


theorem supertrace_odd_square_zero
    (sign : n → ℝ)
    (A : Matrix n n ℝ)
    (hA : IsOdd sign A) :
    supertrace sign (A * A) = 0 := by
  have h := supertrace_mul_comm_of_odd_left sign A A hA
  have hsum : supertrace sign (A * A) + supertrace sign (A * A) = 0 :=
    eq_neg_iff_add_eq_zero.mp h
  have htwo : (2 : ℝ) * supertrace sign (A * A) = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)


theorem supertrace_anticommutator_zero_of_odd_left
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hA : IsOdd sign A) :
    supertrace sign (A * B + B * A) = 0 := by
  rw [supertrace_add, supertrace_mul_comm_of_odd_left sign A B hA]
  simp


theorem supertrace_commutator_zero_of_even_left
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hA : IsEven sign A) :
    supertrace sign (A * B - B * A) = 0 := by
  rw [supertrace_sub, supertrace_mul_comm_of_even_left sign A B hA]
  simp


theorem supertrace_anticommutator_zero_of_odd_right
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hB : IsOdd sign B) :
    supertrace sign (A * B + B * A) = 0 := by
  rw [supertrace_add, supertrace_mul_comm_of_odd_right sign A B hB]
  simp


theorem supertrace_commutator_zero_of_even_right
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hB : IsEven sign B) :
    supertrace sign (A * B - B * A) = 0 := by
  rw [supertrace_sub, supertrace_mul_comm_of_even_right sign A B hB]
  simp


end InfoGeometry.OperatorAlgebra.FiniteParitySupertraceAlgebra
