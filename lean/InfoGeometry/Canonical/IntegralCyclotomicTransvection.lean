/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.IdempotentOrbitContracts
import InfoGeometry.Codes.MajoranaStabilizerThreshold
import Mathlib.GroupTheory.OrderOfElement

/-! # Infinite-order integral transvection recovered from cyclotomic operators

This is an exact integer-matrix specialization, not an exact-order assertion
for arbitrary reflexive pairs or arbitrary characteristic.
-/
namespace InfoGeometry.Canonical.IntegralCyclotomicTransvection
open GrassmannianBundleCyclotomicOrientability
open scoped Matrix

/-- The existing shear is the unipotent of the existing square-zero matrix. -/
theorem matG_eq_one_add : matG = 1 + matD := by decide

/-- The cyclotomic product is precisely the existing ambient shear. -/
theorem cyclotomic_product_eq_shear :
    (-(matD-matB))*(-(matB*matD)+matD-matB)=matG := by
  have h := IdempotentOrbitContracts.cyclotomic_pair_recovers_transvection
    (d := matD) (B := matB) (by decide) (by decide) (by decide)
  have hs : matD*matB+matB*matD=(1 : Mat2Z) := by decide
  rw [hs, ← matG_eq_one_add] at h
  exact h

/-- All powers, not merely a finite regression sample. -/
theorem matG_pow (n : ℕ) : matG^n = !![1, (n : ℤ); 0, 1] := by
  rw [matG_eq_one_add,
    InfoGeometry.Codes.MajoranaStabilizerThreshold.square_zero_unipotent_pow (by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matD]

/-- The upper-right entry recovers the exponent. -/
theorem matG_pow_injective : Function.Injective (fun n : ℕ => matG^n) := by
  intro m n h
  have he := congrArg (fun x : Mat2Z => x 0 1) h
  simp only [matG_pow] at he
  change (m : ℤ) = (n : ℤ) at he
  exact_mod_cast he

/-- Infinite order of the actual unit, rather than just a matrix expression. -/
theorem matGUnit_pow_injective : Function.Injective (fun n : ℕ => matGUnit^n) := by
  intro m n h
  apply matG_pow_injective
  have he := congrArg (fun x : Mat2Zˣ => (x : Mat2Z)) h
  simpa only [Units.val_pow_eq_pow_val, matGUnit] using he

theorem matGUnit_infinite_order : ¬ IsOfFinOrder matGUnit :=
  not_isOfFinOrder_of_injective_pow matGUnit_pow_injective

theorem infinite_matGUnit_powers : Set.Infinite (Set.range (fun n : ℕ => matGUnit^n)) :=
  Set.infinite_range_of_injective matGUnit_pow_injective

end InfoGeometry.Canonical.IntegralCyclotomicTransvection
