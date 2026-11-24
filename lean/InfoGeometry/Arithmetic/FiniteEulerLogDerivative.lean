/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Finite Euler factors and native logarithmic derivatives

This module uses Mathlib's `Derivation` and `Units`. The logarithmic expression
is `u⁻¹ * D u`, with no second derivation or logarithmic-derivative structure.
For an Euler factor `E⁻¹ = 1 - a` and `D a = -ell * a`, its **negative** is
`ell * E * a`. The finite geometric expansion retains its exact remainder.

These algebraic statements neither identify a derivation with differentiation
in the Mellin variable nor pass to an infinite Euler product. The actual zeta
identity for `Re(s) > 1` is owned by
`InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge`.
-/

open scoped BigOperators

namespace InfoGeometry.Arithmetic.FiniteEulerLogDerivative

section NativeDerivation

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- The native derivation gives additive logarithmic velocities on commuting units. -/
theorem units_logDeriv_mul (D : Derivation k R R) (u v : Rˣ) :
    (((u * v)⁻¹ : Rˣ) : R) * D (↑(u * v) : R) =
      ((u⁻¹ : Rˣ) : R) * D (u : R) + ((v⁻¹ : Rˣ) : R) * D (v : R) := by
  simp only [mul_inv_rev, Units.val_mul, D.leibniz, smul_eq_mul]
  calc
    ((v⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R) *
        ((u : R) * D (v : R) + (v : R) * D (u : R)) =
      (((v⁻¹ : Rˣ) : R) * (v : R)) * (((u⁻¹ : Rˣ) : R) * D (u : R)) +
      (((u⁻¹ : Rˣ) : R) * (u : R)) * (((v⁻¹ : Rˣ) : R) * D (v : R)) := by ring
    _ = ((u⁻¹ : Rˣ) : R) * D (u : R) +
        ((v⁻¹ : Rˣ) : R) * D (v : R) := by simp

/-- Inversion reverses the logarithmic velocity, including its sign. -/
theorem units_logDeriv_inv (D : Derivation k R R) (u : Rˣ) :
    (((u⁻¹)⁻¹ : Rˣ) : R) * D ((u⁻¹ : Rˣ) : R) =
      -(((u⁻¹ : Rˣ) : R) * D (u : R)) := by
  have h := units_logDeriv_mul D u u⁻¹
  simp only [mul_inv_cancel, inv_one, Units.val_one, D.map_one_eq_zero,
    mul_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- A finite product becomes a finite sum under the native logarithmic expression. -/
theorem units_logDeriv_prod {ι : Type*} (D : Derivation k R R)
    (S : Finset ι) (E : ι → Rˣ) :
    (((∏ p ∈ S, E p)⁻¹ : Rˣ) : R) * D (↑(∏ p ∈ S, E p) : R) =
      ∑ p ∈ S, ((E p)⁻¹ : Rˣ).val * D ((E p : Rˣ) : R) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.sum_insert hp, units_logDeriv_mul, ih]

/-- With `D a = -ell * a`, the prime-side sign is the negative logarithmic derivative. -/
theorem negative_units_logDeriv_eulerFactor (D : Derivation k R R)
    (E : Rˣ) (a ell : R)
    (hEuler : ((E⁻¹ : Rˣ) : R) = 1 - a)
    (hScale : D a = -ell * a) :
    -(((E⁻¹ : Rˣ) : R) * D (E : R)) = ell * ((E : R) * a) := by
  rw [← units_logDeriv_inv D E, inv_inv, hEuler, D.map_sub,
    D.map_one_eq_zero, hScale]
  ring

/-- The exact finite Euler-product logarithmic derivative, with all local hypotheses explicit. -/
theorem negative_units_logDeriv_eulerProduct {ι : Type*}
    (D : Derivation k R R) (S : Finset ι) (E : ι → Rˣ) (a ell : ι → R)
    (hEuler : ∀ p ∈ S, (((E p)⁻¹ : Rˣ) : R) = 1 - a p)
    (hScale : ∀ p ∈ S, D (a p) = -ell p * a p) :
    -((((∏ p ∈ S, E p)⁻¹ : Rˣ) : R) * D (↑(∏ p ∈ S, E p) : R)) =
      ∑ p ∈ S, ell p * ((E p : R) * a p) := by
  rw [units_logDeriv_prod, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p hp =>
    negative_units_logDeriv_eulerFactor D (E p) (a p) (ell p)
      (hEuler p hp) (hScale p hp)

end NativeDerivation

/-- The prime-power telescoping identity works even in a noncommutative ring. -/
theorem one_sub_mul_sum_powers {R : Type*} [Ring R] (a : R) (M : ℕ) :
    (1 - a) * (∑ j ∈ Finset.range M, a ^ (j + 1)) = a - a ^ (M + 1) := by
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, ← mul_assoc, mul_neg_geom_sum, sub_mul, one_mul]

section EulerRemainder

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- A finite prime-power expansion equals the negative local logarithmic derivative
only after adding its explicit remainder. -/
theorem negative_units_logDeriv_eulerFactor_eq_sum_add_remainder
    (D : Derivation k R R) (E : Rˣ) (a ell : R)
    (hEuler : ((E⁻¹ : Rˣ) : R) = 1 - a)
    (hScale : D a = -ell * a) (M : ℕ) :
    -(((E⁻¹ : Rˣ) : R) * D (E : R)) =
      (∑ j ∈ Finset.range M, ell * a ^ (j + 1)) +
        ell * ((E : R) * a ^ (M + 1)) := by
  have hcancel : (E : R) * (1 - a) = 1 := by
    rw [← hEuler]
    exact Units.mul_inv E
  have hsum := congrArg (fun x : R => (E : R) * x) (one_sub_mul_sum_powers a M)
  rw [← mul_assoc, hcancel, one_mul] at hsum
  rw [negative_units_logDeriv_eulerFactor D E a ell hEuler hScale,
    ← Finset.mul_sum, hsum]
  ring

/-- The complete finite product has an exact finite prime-power expansion with
one displayed remainder for every retained factor. -/
theorem negative_units_logDeriv_eulerProduct_eq_sum_add_remainder {ι : Type*}
    (D : Derivation k R R) (S : Finset ι) (E : ι → Rˣ) (a ell : ι → R)
    (hEuler : ∀ p ∈ S, (((E p)⁻¹ : Rˣ) : R) = 1 - a p)
    (hScale : ∀ p ∈ S, D (a p) = -ell p * a p) (M : ℕ) :
    -((((∏ p ∈ S, E p)⁻¹ : Rˣ) : R) * D (↑(∏ p ∈ S, E p) : R)) =
      ∑ p ∈ S, ((∑ j ∈ Finset.range M, ell p * a p ^ (j + 1)) +
        ell p * ((E p : R) * a p ^ (M + 1))) := by
  rw [units_logDeriv_prod, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p hp =>
    negative_units_logDeriv_eulerFactor_eq_sum_add_remainder D (E p) (a p) (ell p)
      (hEuler p hp) (hScale p hp) M

end EulerRemainder

end InfoGeometry.Arithmetic.FiniteEulerLogDerivative
