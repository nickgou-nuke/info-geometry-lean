import Mathlib

/-!
# Exact 24-fold cyclotomic operator-polynomial spine

This file isolates the rigorous polynomial content of the proposed nested
tripotent/complex/sixfold/eightfold/twelvefold/twenty-fourfold operator picture.

The master polynomial is

`P₂₅(X) = X * (X^24 - 1)`.

We prove its exact factorization through the cyclotomic factors indexed by the
divisors of `24`, prove that the lower stage polynomials divide it, and then
transport those divisibility statements to finite complex operators by
polynomial evaluation.

No claim is made that `P₂₅` is the minimal polynomial of a single physical
operator, nor that the `Φ₁₂` and `Φ₂₄` factors by themselves identify a `G₂`
root system, the Leech lattice, or a Conway-group action.  Those identifications
require independent representation-theoretic owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cyclotomic24OperatorSpine

open Polynomial

/-- The algebraic 25-degree master polynomial: one zero root together with the
24th-root closure. -/
def master25 : ℤ[X] :=
  X * (X ^ 24 - 1)

/-- The fourth cyclotomic polynomial. -/
theorem cyclotomic4_explicit :
    cyclotomic 4 ℤ = X ^ 2 + 1 := by
  have h : 4 = 2 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℤ,
    expand_eq_comp_X_pow, cyclotomic_two]
  simp
  ring

/-- The eighth cyclotomic polynomial. -/
theorem cyclotomic8_explicit :
    cyclotomic 8 ℤ = X ^ 4 + 1 := by
  have h : 8 = 4 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℤ,
    expand_eq_comp_X_pow, cyclotomic4_explicit]
  simp
  ring

/-- The twelfth cyclotomic polynomial. -/
theorem cyclotomic12_explicit :
    cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 := by
  have h : 12 = 6 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℤ,
    expand_eq_comp_X_pow, cyclotomic_six]
  simp
  ring

/-- The twenty-fourth cyclotomic polynomial. -/
theorem cyclotomic24_explicit :
    cyclotomic 24 ℤ = X ^ 8 - X ^ 4 + 1 := by
  have h : 24 = 12 * 2 := by norm_num
  rw [h, ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide) ℤ,
    expand_eq_comp_X_pow, cyclotomic12_explicit]
  simp
  ring

/-- Exact divisor-24 cyclotomic factorization. -/
theorem X24_sub_one_factorization :
    X ^ 24 - 1 =
      cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
      cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 8 ℤ *
      cyclotomic 12 ℤ * cyclotomic 24 ℤ := by
  have h := prod_cyclotomic_eq_X_pow_sub_one (n := 24) (by decide) ℤ
  rw [← h]
  have hdiv : Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} := by
    native_decide
  rw [hdiv]
  simp
  ring

/-- Expanded form of the complete `P₂₅` factorization. -/
theorem master25_cyclotomic_factorization :
    master25 =
      X * cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
      cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 8 ℤ *
      cyclotomic 12 ℤ * cyclotomic 24 ℤ := by
  rw [master25, X24_sub_one_factorization]
  ring

/-- Fully explicit integer-polynomial form of the master factorization. -/
theorem master25_explicit_factorization :
    master25 =
      X * (X - 1) * (X + 1) * (X ^ 2 + X + 1) *
      (X ^ 2 + 1) * (X ^ 2 - X + 1) * (X ^ 4 + 1) *
      (X ^ 4 - X ^ 2 + 1) * (X ^ 8 - X ^ 4 + 1) := by
  rw [master25_cyclotomic_factorization,
    cyclotomic_one, cyclotomic_two, cyclotomic_three, cyclotomic_six,
    cyclotomic4_explicit, cyclotomic8_explicit,
    cyclotomic12_explicit, cyclotomic24_explicit]

/-- The tripotent annihilator is exactly the zero/`±1` cyclotomic sector. -/
theorem tripotent_polynomial_factorization :
    X ^ 3 - X = X * cyclotomic 1 ℤ * cyclotomic 2 ℤ := by
  rw [cyclotomic_one, cyclotomic_two]
  ring

/-- The `0, ±i` cubic annihilator is the zero sector times `Φ₄`. -/
theorem complex_structure_polynomial_factorization :
    X ^ 3 + X = X * cyclotomic 4 ℤ := by
  rw [cyclotomic4_explicit]
  ring

/-- The sixfold root closure contains exactly `Φ₁ Φ₂ Φ₃ Φ₆`. -/
theorem X6_sub_one_factorization :
    X ^ 6 - 1 =
      cyclotomic 1 ℤ * cyclotomic 2 ℤ *
      cyclotomic 3 ℤ * cyclotomic 6 ℤ := by
  rw [cyclotomic_one, cyclotomic_two, cyclotomic_three, cyclotomic_six]
  ring

/-- The twelvefold root closure contains the divisor-12 cyclotomic sectors. -/
theorem X12_sub_one_factorization :
    X ^ 12 - 1 =
      cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
      cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 12 ℤ := by
  rw [cyclotomic_one, cyclotomic_two, cyclotomic_three, cyclotomic_six,
    cyclotomic4_explicit, cyclotomic12_explicit]
  ring

/-- The tripotent stage polynomial divides the master closure. -/
theorem tripotent_dvd_master25 :
    X ^ 3 - X ∣ master25 := by
  rw [tripotent_polynomial_factorization,
    master25_cyclotomic_factorization]
  refine ⟨cyclotomic 3 ℤ * cyclotomic 4 ℤ * cyclotomic 6 ℤ *
    cyclotomic 8 ℤ * cyclotomic 12 ℤ * cyclotomic 24 ℤ, ?_⟩
  ring

/-- The complex-structure stage polynomial divides the master closure. -/
theorem complex_structure_dvd_master25 :
    X ^ 3 + X ∣ master25 := by
  rw [complex_structure_polynomial_factorization,
    master25_cyclotomic_factorization]
  refine ⟨cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
    cyclotomic 6 ℤ * cyclotomic 8 ℤ * cyclotomic 12 ℤ *
    cyclotomic 24 ℤ, ?_⟩
  ring

/-- `Φ₈ = X⁴+1` is one of the exact master factors. -/
theorem phi8_dvd_master25 :
    X ^ 4 + 1 ∣ master25 := by
  rw [← cyclotomic8_explicit, master25_cyclotomic_factorization]
  refine ⟨X * cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
    cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 12 ℤ *
    cyclotomic 24 ℤ, ?_⟩
  ring

/-- The sixfold closure divides the master closure. -/
theorem X6_sub_one_dvd_master25 :
    X ^ 6 - 1 ∣ master25 := by
  rw [X6_sub_one_factorization, master25_cyclotomic_factorization]
  refine ⟨X * cyclotomic 4 ℤ * cyclotomic 8 ℤ *
    cyclotomic 12 ℤ * cyclotomic 24 ℤ, ?_⟩
  ring

/-- The twelvefold closure divides the master closure. -/
theorem X12_sub_one_dvd_master25 :
    X ^ 12 - 1 ∣ master25 := by
  rw [X12_sub_one_factorization, master25_cyclotomic_factorization]
  refine ⟨X * cyclotomic 8 ℤ * cyclotomic 24 ℤ, ?_⟩
  ring

/-- `Φ₂₄ = X⁸-X⁴+1` is one of the exact master factors. -/
theorem phi24_dvd_master25 :
    X ^ 8 - X ^ 4 + 1 ∣ master25 := by
  rw [← cyclotomic24_explicit, master25_cyclotomic_factorization]
  refine ⟨X * cyclotomic 1 ℤ * cyclotomic 2 ℤ * cyclotomic 3 ℤ *
    cyclotomic 4 ℤ * cyclotomic 6 ℤ * cyclotomic 8 ℤ *
    cyclotomic 12 ℤ, ?_⟩
  ring

/-- Compact nested-factor packet.  This is a divisibility statement only; it
makes no spectral-realization claim about a particular operator. -/
theorem cyclotomic24_nested_factor_packet :
    (X ^ 3 - X ∣ master25) ∧
    (X ^ 3 + X ∣ master25) ∧
    (X ^ 4 + 1 ∣ master25) ∧
    (X ^ 6 - 1 ∣ master25) ∧
    (X ^ 12 - 1 ∣ master25) ∧
    (X ^ 8 - X ^ 4 + 1 ∣ master25) := by
  exact ⟨tripotent_dvd_master25,
    complex_structure_dvd_master25,
    phi8_dvd_master25,
    X6_sub_one_dvd_master25,
    X12_sub_one_dvd_master25,
    phi24_dvd_master25⟩

/-! ## Finite operator realization of the annihilator spine -/

/-- Complex-coefficient version of the master polynomial, used for finite
complex matrix evaluation. -/
def master25C : ℂ[X] :=
  X * (X ^ 24 - 1)

/-- Any polynomial factor annihilating an operator also forces the master
polynomial to annihilate it, provided that factor divides the master polynomial. -/
theorem aeval_master25C_eq_zero_of_dvd
    {n : ℕ} (p : ℂ[X])
    (hp : p ∣ master25C)
    (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : aeval T p = 0) :
    aeval T master25C = 0 := by
  rcases hp with ⟨q, rfl⟩
  rw [map_mul, hT, zero_mul]

/-- The tripotent polynomial divides the complex master polynomial. -/
theorem tripotent_dvd_master25C :
    X ^ 3 - X ∣ master25C := by
  refine ⟨(X ^ 22 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 12 +
      X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + 1) : ℂ[X], ?_⟩
  simp [master25C]
  ring

/-- The `0,±i` cubic polynomial divides the complex master polynomial. -/
theorem complex_structure_dvd_master25C :
    X ^ 3 + X ∣ master25C := by
  refine ⟨(X ^ 22 - X ^ 20 + X ^ 18 - X ^ 16 + X ^ 14 - X ^ 12 +
      X ^ 10 - X ^ 8 + X ^ 6 - X ^ 4 + X ^ 2 - 1) : ℂ[X], ?_⟩
  simp [master25C]
  ring

/-- The eighth-cyclotomic stage divides the complex master polynomial. -/
theorem phi8_dvd_master25C :
    X ^ 4 + 1 ∣ master25C := by
  refine ⟨(X * (X ^ 20 - X ^ 16 + X ^ 12 - X ^ 8 + X ^ 4 - 1)) : ℂ[X], ?_⟩
  simp [master25C]
  ring

/-- The sixfold closure divides the complex master polynomial. -/
theorem X6_sub_one_dvd_master25C :
    X ^ 6 - 1 ∣ master25C := by
  refine ⟨(X * (X ^ 18 + X ^ 12 + X ^ 6 + 1)) : ℂ[X], ?_⟩
  simp [master25C]
  ring

/-- The twelvefold closure divides the complex master polynomial. -/
theorem X12_sub_one_dvd_master25C :
    X ^ 12 - 1 ∣ master25C := by
  refine ⟨(X * (X ^ 12 + 1)) : ℂ[X], ?_⟩
  simp [master25C]
  ring

/-- The primitive 24th cyclotomic factor divides the complex master polynomial. -/
theorem phi24_dvd_master25C :
    X ^ 8 - X ^ 4 + 1 ∣ master25C := by
  refine ⟨(X * (X ^ 16 + X ^ 12 - X ^ 4 - 1)) : ℂ[X], ?_⟩
  simp [master25C]
  ring

/-- A tripotent finite operator is annihilated by the master polynomial. -/
theorem master25C_annihilates_of_tripotent
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ^ 3 = T) :
    aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 3 - X) tripotent_dvd_master25C T
  simp [hT]

/-- A finite operator satisfying `T³ = -T` is annihilated by the master polynomial. -/
theorem master25C_annihilates_of_complex_structure
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ^ 3 = -T) :
    aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 3 + X) complex_structure_dvd_master25C T
  simp [hT]

/-- A finite `Φ₈` operator is annihilated by the master polynomial. -/
theorem master25C_annihilates_of_phi8
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ^ 4 = -1) :
    aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 4 + 1) phi8_dvd_master25C T
  simp [hT]

/-- A sixfold finite operator is annihilated by the master polynomial. -/
theorem master25C_annihilates_of_order6
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ^ 6 = 1) :
    aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 6 - 1) X6_sub_one_dvd_master25C T
  simp [hT]

/-- A twelvefold finite operator is annihilated by the master polynomial. -/
theorem master25C_annihilates_of_order12
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ^ 12 = 1) :
    aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd (X ^ 12 - 1) X12_sub_one_dvd_master25C T
  simp [hT]

/-- A primitive-24-factor finite operator is annihilated by the master polynomial. -/
theorem master25C_annihilates_of_phi24
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ^ 8 - T ^ 4 + 1 = 0) :
    aeval T master25C = 0 := by
  apply aeval_master25C_eq_zero_of_dvd
    (X ^ 8 - X ^ 4 + 1) phi24_dvd_master25C T
  simpa using hT

/-- Direct master closure: every finite operator of order dividing 24 is
annihilated by `P₂₅`. -/
theorem master25C_annihilates_of_order24
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T ^ 24 = 1) :
    aeval T master25C = 0 := by
  simp [master25C, hT]

/-- Compact operator-level closure packet.  Each implication is conditional on
an explicit annihilator equation for the supplied finite operator. -/
theorem cyclotomic24_operator_annihilator_packet
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    (T ^ 3 = T → aeval T master25C = 0) ∧
    (T ^ 3 = -T → aeval T master25C = 0) ∧
    (T ^ 4 = -1 → aeval T master25C = 0) ∧
    (T ^ 6 = 1 → aeval T master25C = 0) ∧
    (T ^ 12 = 1 → aeval T master25C = 0) ∧
    (T ^ 24 = 1 → aeval T master25C = 0) := by
  exact ⟨master25C_annihilates_of_tripotent T,
    master25C_annihilates_of_complex_structure T,
    master25C_annihilates_of_phi8 T,
    master25C_annihilates_of_order6 T,
    master25C_annihilates_of_order12 T,
    master25C_annihilates_of_order24 T⟩

end InfoGeometry.Canonical.Cyclotomic24OperatorSpine
