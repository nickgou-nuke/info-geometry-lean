/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

namespace InfoGeometry.Algebra.FiniteFieldFrobenius

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

end InfoGeometry.Algebra.FiniteFieldFrobenius
