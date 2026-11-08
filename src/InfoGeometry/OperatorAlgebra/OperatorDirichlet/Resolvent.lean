/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Resolvents, periodic averages, and cyclotomic annihilation in a non-commutative ring

All statements are about one or two elements of an arbitrary ring `A`; no
commutativity of `A` is assumed.

1. **Geometric resolvent.** If `x ^ n = 0`, then `1 - x` is invertible with
   inverse `∑_{k<n} x^k`.
2. **Periodic average.** If `T ^ n = 1` and `E = ∑_{k<n} T^k`, then
   `T E = E T = E` and `E E = n • E`. So `E` is `n` times an idempotent: it
   picks out the fixed vectors of `T`, like a delta function at eigenvalue `1`.
3. **Cyclotomic annihilation.** `∏_{d ∣ n} Φ_d(T) = T^n - 1`. In particular a
   periodic operator is annihilated by the product of the cyclotomic polynomials
   of the divisors of its period.
4. **Operator-coefficient characteristic polynomial.** If `Φ * Φ = V`, then
   `(z - Φ)(z + Φ) = z² - V`. Whenever `z² - V` is a unit, the resolvent is
   `(z - Φ)⁻¹ = (z + Φ)(z² - V)⁻¹`. Here `V` is an operator, not a scalar.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorDirichlet

open Finset Polynomial

variable {A : Type*} [Ring A]

/-! ### Geometric resolvent of a nilpotent element -/

theorem one_sub_mul_geom_of_pow_eq_zero {x : A} {n : ℕ} (hx : x ^ n = 0) :
    (1 - x) * (∑ k ∈ range n, x ^ k) = 1 ∧ (∑ k ∈ range n, x ^ k) * (1 - x) = 1 := by
  have h1 := mul_geom_sum x n
  have h2 := geom_sum_mul x n
  rw [hx] at h1 h2
  constructor
  · have : (1 - x) * ∑ k ∈ range n, x ^ k = -((x - 1) * ∑ k ∈ range n, x ^ k) := by noncomm_ring
    rw [this, h1, zero_sub, neg_neg]
  · have : (∑ k ∈ range n, x ^ k) * (1 - x) = -((∑ k ∈ range n, x ^ k) * (x - 1)) := by
      noncomm_ring
    rw [this, h2, zero_sub, neg_neg]

/-- The resolvent of a nilpotent element as a unit. -/
def nilpotentResolvent {x : A} {n : ℕ} (hx : x ^ n = 0) : Aˣ where
  val := 1 - x
  inv := ∑ k ∈ range n, x ^ k
  val_inv := (one_sub_mul_geom_of_pow_eq_zero hx).1
  inv_val := (one_sub_mul_geom_of_pow_eq_zero hx).2

/-! ### Periodic averages -/

section Periodic

variable {T : A} {n : ℕ} (hT : T ^ n = 1)
include hT

theorem mul_periodicAverage : T * (∑ k ∈ range n, T ^ k) = ∑ k ∈ range n, T ^ k := by
  have h := mul_geom_sum T n
  rw [hT, sub_self, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem periodicAverage_mul : (∑ k ∈ range n, T ^ k) * T = ∑ k ∈ range n, T ^ k := by
  have h := geom_sum_mul T n
  rw [hT, sub_self, mul_sub, mul_one, sub_eq_zero] at h
  exact h

theorem pow_mul_periodicAverage (j : ℕ) :
    T ^ j * (∑ k ∈ range n, T ^ k) = ∑ k ∈ range n, T ^ k := by
  induction j with
  | zero => rw [pow_zero, one_mul]
  | succ j ih => rw [pow_succ', mul_assoc, ih, mul_periodicAverage hT]

/-- `E E = n • E`: the periodic average is `n` times an idempotent. -/
theorem periodicAverage_mul_self :
    (∑ k ∈ range n, T ^ k) * (∑ k ∈ range n, T ^ k) = n • ∑ k ∈ range n, T ^ k := by
  rw [Finset.sum_mul]
  simp_rw [pow_mul_periodicAverage hT]
  rw [Finset.sum_const, card_range]

end Periodic

/-! ### Cyclotomic annihilation -/

/-- The product of the cyclotomic polynomials over the divisors of `n`,
evaluated at an operator `T`, is `T ^ n - 1`. -/
theorem aeval_prod_cyclotomic {n : ℕ} (hn : 0 < n) (T : A) :
    aeval T (∏ d ∈ n.divisors, cyclotomic d ℤ) = T ^ n - 1 := by
  rw [prod_cyclotomic_eq_X_pow_sub_one hn ℤ]
  simp

theorem aeval_prod_cyclotomic_eq_zero {n : ℕ} (hn : 0 < n) {T : A} (hT : T ^ n = 1) :
    aeval T (∏ d ∈ n.divisors, cyclotomic d ℤ) = 0 := by
  rw [aeval_prod_cyclotomic hn, hT, sub_self]

/-! ### Operator-coefficient characteristic polynomial and resolvent -/

section CharPoly

variable {R : Type*} [CommRing R] [Algebra R A] {Φ V : A} (hΦ : Φ * Φ = V)
include hΦ

theorem commute_square : Commute Φ V := by
  rw [← hΦ]; exact (Commute.refl Φ).mul_right (Commute.refl Φ)

/-- `(z - Φ)(z + Φ) = z² - V` with operator-valued `V`. -/
theorem charPoly_factor (z : R) :
    (algebraMap R A z - Φ) * (algebraMap R A z + Φ) = algebraMap R A (z * z) - V := by
  rw [← hΦ, map_mul]
  have hc : Φ * algebraMap R A z = algebraMap R A z * Φ := (Algebra.commutes z Φ).symm
  noncomm_ring [hc]

theorem charPoly_factor' (z : R) :
    (algebraMap R A z + Φ) * (algebraMap R A z - Φ) = algebraMap R A (z * z) - V := by
  rw [← hΦ, map_mul]
  have hc : Φ * algebraMap R A z = algebraMap R A z * Φ := (Algebra.commutes z Φ).symm
  noncomm_ring [hc]

/-- The resolvent of `Φ` from the inverse of its operator characteristic value. -/
theorem resolvent_of_charPoly_unit (z : R) (u : Aˣ) (hu : (u : A) = algebraMap R A (z * z) - V) :
    (algebraMap R A z - Φ) * ((algebraMap R A z + Φ) * ↑u⁻¹) = 1 ∧
    ((algebraMap R A z + Φ) * ↑u⁻¹) * (algebraMap R A z - Φ) = 1 := by
  have hcu : Commute (u : A) (algebraMap R A z - Φ) := by
    rw [hu]
    exact (Algebra.commute_algebraMap_left (z * z) _).sub_left
      ((Algebra.commute_algebraMap_right z V).sub_right (commute_square hΦ).symm)
  constructor
  · rw [← mul_assoc, charPoly_factor hΦ, ← hu, Units.mul_inv]
  · rw [mul_assoc, (hcu.units_inv_left).eq, ← mul_assoc, charPoly_factor' hΦ, ← hu,
      Units.mul_inv]

end CharPoly

end InfoGeometry.OperatorAlgebra.OperatorDirichlet
