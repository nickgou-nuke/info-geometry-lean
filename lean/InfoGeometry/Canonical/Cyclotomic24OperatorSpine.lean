/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CyclotomicOperatorSpine

/-!
# Compatibility and integer-polynomial view of the 24-fold spine

The operator-level owner is `CyclotomicOperatorSpine`.  This file supplies
the upstream integer-polynomial presentation without asserting a spectral
realization for any particular physical operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cyclotomic24OperatorSpine

open Polynomial

def master25 : ℤ[X] := X * (X ^ 24 - 1)

theorem master25_explicit_factorization :
    master25 = X * (X - 1) * (X + 1) * (X ^ 2 + X + 1) *
      (X ^ 2 + 1) * (X ^ 2 - X + 1) * (X ^ 4 + 1) *
      (X ^ 4 - X ^ 2 + 1) * (X ^ 8 - X ^ 4 + 1) := by
  unfold master25
  ring

theorem tripotent_dvd_master25 : X ^ 3 - X ∣ master25 := by
  refine ⟨X ^ 22 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 12 +
      X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + 1, ?_⟩
  unfold master25
  ring

theorem phi24_dvd_master25 : X ^ 8 - X ^ 4 + 1 ∣ master25 := by
  refine ⟨X * (X ^ 16 + X ^ 12 - X ^ 4 - 1), ?_⟩
  unfold master25
  ring


theorem cyclotomic4_explicit : cyclotomic 4 ℤ = X ^ 2 + 1 := by
  have h : 4 = 2 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℤ,
    expand_eq_comp_X_pow, cyclotomic_two]
  simp

theorem cyclotomic8_explicit : cyclotomic 8 ℤ = X ^ 4 + 1 := by
  have h : 8 = 4 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℤ,
    expand_eq_comp_X_pow, cyclotomic4_explicit]
  simp
  ring

theorem cyclotomic12_explicit : cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 := by
  have h : 12 = 6 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℤ,
    expand_eq_comp_X_pow, cyclotomic_six]
  simp
  ring

theorem cyclotomic24_explicit : cyclotomic 24 ℤ = X ^ 8 - X ^ 4 + 1 := by
  have h : 24 = 12 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℤ,
    expand_eq_comp_X_pow, cyclotomic12_explicit]
  simp
  ring

theorem X24_sub_one_factorization :
    X ^ 24 - 1 =
      cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
      cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 8 ℤ *
      cyclotomic 12 ℤ * cyclotomic 24 ℤ := by
  have h := prod_cyclotomic_eq_X_pow_sub_one (n := 24) (by decide) ℤ
  rw [← h]
  have hdiv : Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
  rw [hdiv]
  simp
  ring

theorem master25_cyclotomic_factorization :
    master25 =
      X * cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
      cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 8 ℤ *
      cyclotomic 12 ℤ * cyclotomic 24 ℤ := by
  rw [master25, X24_sub_one_factorization]
  ring

theorem tripotent_polynomial_factorization :
    X ^ 3 - X = X * cyclotomic 1 ℤ * cyclotomic 2 ℤ := by
  rw [cyclotomic_one, cyclotomic_two]
  ring

theorem complex_structure_polynomial_factorization :
    X ^ 3 + X = X * cyclotomic 4 ℤ := by
  rw [cyclotomic4_explicit]
  ring

theorem X6_sub_one_factorization :
    X ^ 6 - 1 = cyclotomic 1 ℤ * cyclotomic 2 ℤ *
      cyclotomic 3 ℤ * cyclotomic 6 ℤ := by
  rw [cyclotomic_one, cyclotomic_two, cyclotomic_three, cyclotomic_six]
  ring

theorem X12_sub_one_factorization :
    X ^ 12 - 1 = cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
      cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 12 ℤ := by
  rw [cyclotomic_one, cyclotomic_two, cyclotomic_three, cyclotomic_six,
    cyclotomic4_explicit, cyclotomic12_explicit]
  ring

theorem complex_structure_dvd_master25 : X ^ 3 + X ∣ master25 := by
  rw [complex_structure_polynomial_factorization, master25_cyclotomic_factorization]
  refine ⟨cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
    cyclotomic 6 ℤ * cyclotomic 8 ℤ * cyclotomic 12 ℤ * cyclotomic 24 ℤ, ?_⟩
  ring

theorem phi8_dvd_master25 : X ^ 4 + 1 ∣ master25 := by
  rw [← cyclotomic8_explicit, master25_cyclotomic_factorization]
  refine ⟨X * cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
    cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 12 ℤ * cyclotomic 24 ℤ, ?_⟩
  ring

theorem X6_sub_one_dvd_master25 : X ^ 6 - 1 ∣ master25 := by
  rw [X6_sub_one_factorization, master25_cyclotomic_factorization]
  refine ⟨X * cyclotomic 4 ℤ * cyclotomic 8 ℤ * cyclotomic 12 ℤ *
    cyclotomic 24 ℤ, ?_⟩
  ring

theorem X12_sub_one_dvd_master25 : X ^ 12 - 1 ∣ master25 := by
  rw [X12_sub_one_factorization, master25_cyclotomic_factorization]
  refine ⟨X * cyclotomic 8 ℤ * cyclotomic 24 ℤ, ?_⟩
  ring

theorem cyclotomic24_nested_factor_packet :
    (X ^ 3 - X ∣ master25) ∧ (X ^ 3 + X ∣ master25) ∧
    (X ^ 4 + 1 ∣ master25) ∧ (X ^ 6 - 1 ∣ master25) ∧
    (X ^ 12 - 1 ∣ master25) ∧ (X ^ 8 - X ^ 4 + 1 ∣ master25) := by
  exact ⟨tripotent_dvd_master25, complex_structure_dvd_master25,
    phi8_dvd_master25, X6_sub_one_dvd_master25, X12_sub_one_dvd_master25,
    phi24_dvd_master25⟩

def master25C : ℂ[X] := X * (X ^ 24 - 1)

theorem aeval_master25C_eq_zero_of_dvd {n : ℕ} (p : ℂ[X])
    (hp : p ∣ master25C) (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : aeval T p = 0) : aeval T master25C = 0 := by
  rcases hp with ⟨q, hq⟩
  rw [hq, map_mul, hT, zero_mul]

theorem tripotent_dvd_master25C : X ^ 3 - X ∣ master25C := by
  let q : ℂ[X] := X ^ 22 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 12 +
      X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + 1
  refine ⟨q, ?_⟩
  simp [master25C, q]
  ring

theorem complex_structure_dvd_master25C : X ^ 3 + X ∣ master25C := by
  let q : ℂ[X] := X ^ 22 - X ^ 20 + X ^ 18 - X ^ 16 + X ^ 14 - X ^ 12 +
      X ^ 10 - X ^ 8 + X ^ 6 - X ^ 4 + X ^ 2 - 1
  refine ⟨q, ?_⟩
  simp [master25C, q]
  ring

theorem phi8_dvd_master25C : X ^ 4 + 1 ∣ master25C := by
  let q : ℂ[X] := X * (X ^ 20 - X ^ 16 + X ^ 12 - X ^ 8 + X ^ 4 - 1)
  refine ⟨q, ?_⟩
  simp [master25C, q]
  ring

theorem X6_sub_one_dvd_master25C : X ^ 6 - 1 ∣ master25C := by
  let q : ℂ[X] := X * (X ^ 18 + X ^ 12 + X ^ 6 + 1)
  refine ⟨q, ?_⟩
  simp [master25C, q]
  ring

theorem X12_sub_one_dvd_master25C : X ^ 12 - 1 ∣ master25C := by
  let q : ℂ[X] := X * (X ^ 12 + 1)
  refine ⟨q, ?_⟩
  simp [master25C, q]
  ring

theorem phi24_dvd_master25C : X ^ 8 - X ^ 4 + 1 ∣ master25C := by
  let q : ℂ[X] := X * (X ^ 16 + X ^ 12 - X ^ 4 - 1)
  refine ⟨q, ?_⟩
  simp [master25C, q]
  ring

theorem master25C_annihilates_of_tripotent {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T ^ 3 = T) : aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 3 - X) tripotent_dvd_master25C T
  simp [hT]

theorem master25C_annihilates_of_complex_structure {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T ^ 3 = -T) : aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 3 + X) complex_structure_dvd_master25C T
  simp [hT]

theorem master25C_annihilates_of_phi8 {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T ^ 4 = -1) : aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 4 + 1) phi8_dvd_master25C T
  simp [hT]

theorem master25C_annihilates_of_order6 {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T ^ 6 = 1) : aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 6 - 1) X6_sub_one_dvd_master25C T
  simp [hT]

theorem master25C_annihilates_of_order12 {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T ^ 12 = 1) : aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 12 - 1) X12_sub_one_dvd_master25C T
  simp [hT]

theorem master25C_annihilates_of_phi24 {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T ^ 8 - T ^ 4 + 1 = 0) : aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 8 - X ^ 4 + 1) phi24_dvd_master25C T
  simpa using hT

theorem master25C_annihilates_of_order24 {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T ^ 24 = 1) : aeval T master25C = 0 := by
  simp [master25C, hT]

theorem cyclotomic24_operator_annihilator_packet {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    (T ^ 3 = T → aeval T master25C = 0) ∧
    (T ^ 3 = -T → aeval T master25C = 0) ∧
    (T ^ 4 = -1 → aeval T master25C = 0) ∧
    (T ^ 6 = 1 → aeval T master25C = 0) ∧
    (T ^ 12 = 1 → aeval T master25C = 0) ∧
    (T ^ 24 = 1 → aeval T master25C = 0) := by
  exact ⟨master25C_annihilates_of_tripotent T,
    master25C_annihilates_of_complex_structure T,
    master25C_annihilates_of_phi8 T, master25C_annihilates_of_order6 T,
    master25C_annihilates_of_order12 T, master25C_annihilates_of_order24 T⟩

end InfoGeometry.Canonical.Cyclotomic24OperatorSpine
