import InfoGeometry.Nuclear.WaleckaZornBdG
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Nuclear.WaleckaZornBdG

open InfoGeometry.Nuclear.NambuGorkov
open scoped BigOperators

noncomputable section

theorem one_sub_mul_one_add {A : Type*} [Ring A] (x : A) :
    (1 - x) * (1 + x) = 1 - x * x := by
  calc
    (1 - x) * (1 + x) = (1 + x) - x * (1 + x) := by rw [one_sub_mul]
    _ = 1 - x * x := by rw [mul_one_add]; abel

theorem one_add_mul_one_sub {A : Type*} [Ring A] (x : A) :
    (1 + x) * (1 - x) = (1 - x) * (1 + x) := by
  rw [one_sub_mul_one_add]
  noncomm_ring

theorem regularHamiltonian_pow_even (state : NambuGorkovCarrier ℝ) (order : ℕ) :
    regularHamiltonian state ^ (2 * order) =
      ((bogoliubovEnergy state) ^ 2) ^ order •
        (1 : Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ)) := by
  rw [pow_mul, pow_two, regularHamiltonian_square, smul_pow, one_pow]

theorem regularHamiltonian_pow_odd (state : NambuGorkovCarrier ℝ) (order : ℕ) :
    regularHamiltonian state ^ (2 * order + 1) =
      ((bogoliubovEnergy state) ^ 2) ^ order • regularHamiltonian state := by
  rw [pow_succ, regularHamiltonian_pow_even, smul_mul_assoc, one_mul]

theorem regularHamiltonian_finite_series (state : NambuGorkovCarrier ℝ)
    (coefficients : ℕ → ℝ) (order : ℕ) :
    (∑ index ∈ Finset.range order,
      (coefficients (2 * index) • regularHamiltonian state ^ (2 * index) +
        coefficients (2 * index + 1) • regularHamiltonian state ^ (2 * index + 1))) =
      (∑ index ∈ Finset.range order,
        coefficients (2 * index) * ((bogoliubovEnergy state) ^ 2) ^ index) •
          (1 : Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ)) +
      (∑ index ∈ Finset.range order,
        coefficients (2 * index + 1) * ((bogoliubovEnergy state) ^ 2) ^ index) •
          regularHamiltonian state := by
  simp only [regularHamiltonian_pow_even, regularHamiltonian_pow_odd,
    smul_smul, Finset.sum_add_distrib, Finset.sum_smul]

theorem regularHamiltonian_shift_product (state : NambuGorkovCarrier ℝ)
    (parameter : ℝ) :
    (1 - parameter • regularHamiltonian state) *
        (1 + parameter • regularHamiltonian state) =
      (1 - parameter ^ 2 * (bogoliubovEnergy state) ^ 2) •
        (1 : Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ)) := by
  let H : Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ) :=
    parameter • regularHamiltonian state
  have hHsq : H * H =
      (parameter ^ 2 * (bogoliubovEnergy state) ^ 2) •
        (1 : Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ)) := by
    dsimp [H]
    rw [smul_mul_smul_comm, regularHamiltonian_square, smul_smul]
    congr 1
    ring
  calc
    _ = 1 - H * H := one_sub_mul_one_add H
    _ = _ := by
      rw [hHsq, sub_smul, one_smul]

theorem regularHamiltonian_shift_product_reverse (state : NambuGorkovCarrier ℝ)
    (parameter : ℝ) :
    (1 + parameter • regularHamiltonian state) *
        (1 - parameter • regularHamiltonian state) =
      (1 - parameter ^ 2 * (bogoliubovEnergy state) ^ 2) •
        (1 : Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ)) := by
  let H : Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ) :=
    parameter • regularHamiltonian state
  calc
    _ = (1 - H) * (1 + H) := one_add_mul_one_sub H
    _ = _ := regularHamiltonian_shift_product state parameter

def regularHamiltonianResolventUnit (state : NambuGorkovCarrier ℝ) (parameter : ℝ)
    (nonresonant : 1 - parameter ^ 2 * (bogoliubovEnergy state) ^ 2 ≠ 0) :
    (Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ))ˣ where
  val := 1 - parameter • regularHamiltonian state
  inv := (1 - parameter ^ 2 * (bogoliubovEnergy state) ^ 2)⁻¹ •
    (1 + parameter • regularHamiltonian state)
  val_inv := by
    rw [mul_smul_comm, regularHamiltonian_shift_product, smul_smul,
      inv_mul_cancel₀ nonresonant, one_smul]
  inv_val := by
    rw [smul_mul_assoc, regularHamiltonian_shift_product_reverse, smul_smul,
      inv_mul_cancel₀ nonresonant, one_smul]

end

end InfoGeometry.Nuclear.WaleckaZornBdG
