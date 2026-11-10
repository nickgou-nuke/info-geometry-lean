/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.FiniteFieldFrobenius

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

/-- A concrete Mathlib model of the degree-three extension of `𝔽₂`. -/
abbrev F8 := FiniteField.Extension (ZMod 2) 2 3

noncomputable instance : Fintype F8 := Fintype.ofFinite F8

theorem f8_card : Fintype.card F8 = 8 := by
  rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension]
  norm_num

/-- In any finite `[DivisionRing D]`, every nonzero element `x ≠ 0` satisfies
`x ^ (Fintype.card D - 1) = 1` via Lagrange's theorem on the multiplicative group `Dˣ`. -/
theorem pow_card_sub_one_eq_one_divisionRing {D : Type*} [DivisionRing D] [Fintype D]
    {x : D} (hx : x ≠ 0) :
    x ^ (Fintype.card D - 1) = 1 := by
  classical
  have hu : (Units.mk0 x hx) ^ Fintype.card Dˣ = 1 := pow_card_eq_one
  have hval := congrArg (fun u : Dˣ => (u : D)) hu
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, Fintype.card_units] at hval
  exact hval

/-- In any finite `[DivisionRing D]`, every element satisfies `x ^ Fintype.card D = x`. -/
theorem pow_card_eq_self_divisionRing {D : Type*} [DivisionRing D] [Fintype D] (x : D) :
    x ^ Fintype.card D = x := by
  by_cases hx : x = 0
  · subst hx
    exact zero_pow Fintype.card_ne_zero
  · have hcard : Fintype.card D - 1 + 1 = Fintype.card D :=
      Nat.sub_add_cancel Fintype.card_pos
    calc
      x ^ Fintype.card D = x ^ (Fintype.card D - 1 + 1) := by rw [hcard]
      _ = x ^ (Fintype.card D - 1) * x := pow_succ x (Fintype.card D - 1)
      _ = 1 * x := by rw [pow_card_sub_one_eq_one_divisionRing hx]
      _ = x := one_mul x

/-- A finite `[DivisionRing D]` with eight elements satisfies `x ^ 8 = x`. -/
theorem pow_eight_eq_self_divisionRing {D : Type*} [DivisionRing D] [Fintype D]
    (hcard : Fintype.card D = 8) (x : D) :
    x ^ 8 = x := by
  rw [← hcard]
  exact pow_card_eq_self_divisionRing x

/-- The nonzero part of an eight-element `[DivisionRing D]` has exponent seven. -/
theorem nonzero_pow_seven_eq_one_divisionRing {D : Type*} [DivisionRing D] [Fintype D]
    (hcard : Fintype.card D = 8) {x : D} (hx : x ≠ 0) :
    x ^ 7 = 1 := by
  have h := pow_card_sub_one_eq_one_divisionRing hx
  rw [hcard] at h
  simpa using h

/-- Frobenius identity for every finite field, in its native Mathlib form. -/
theorem pow_card_eq_self {F : Type*} [Field F] [Fintype F] (x : F) :
    x ^ Fintype.card F = x := by
  exact FiniteField.pow_card x

/-- A finite field with eight elements satisfies the defining equation of `F₈`.

The theorem is intentionally parameterized by the field carrier; no arbitrary
concrete model of `F₈` is introduced here. -/
theorem pow_eight_eq_self {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 8) (x : F) :
    x ^ 8 = x := by
  rw [← hcard]
  exact pow_card_eq_self x

/-- The nonzero part of an eight-element field has exponent seven. -/
theorem nonzero_pow_seven_eq_one {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 8) {x : F} (hx : x ≠ 0) :
    x ^ 7 = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rw [hcard] at h
  simpa using h

/-- The Frobenius identity on the concrete eight-element carrier. -/
theorem f8_pow_eight_eq_self (x : F8) :
    x ^ 8 = x := by
  exact pow_eight_eq_self f8_card x

end InfoGeometry.Algebra.FiniteFieldFrobenius
