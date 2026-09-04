import Mathlib

/-!
# Exact 24-fold cyclotomic operator-polynomial spine

This file isolates the rigorous polynomial content of the proposed nested
tripotent/complex/sixfold/eightfold/twelvefold/twenty-fourfold operator picture.

The master polynomial is

`P₂₅(X) = X * (X^24 - 1)`.

We prove its exact factorization through the cyclotomic factors indexed by the
divisors of `24`, and prove that the lower stage polynomials divide it.

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

end InfoGeometry.Canonical.Cyclotomic24OperatorSpine
