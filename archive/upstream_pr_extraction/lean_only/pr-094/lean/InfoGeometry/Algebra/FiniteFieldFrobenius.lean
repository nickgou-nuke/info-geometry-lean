/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

namespace InfoGeometry.Algebra.FiniteFieldFrobenius

/-- A concrete Mathlib model of the degree-three extension of `𝔽₂`. -/
abbrev F8 := FiniteField.Extension (ZMod 2) 2 3

noncomputable instance : Fintype F8 := Fintype.ofFinite F8

theorem f8_card : Fintype.card F8 = 8 := by
  rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension]
  norm_num

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
