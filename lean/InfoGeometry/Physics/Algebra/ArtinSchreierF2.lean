/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# The Artin--Schreier polynomial over `𝔽₂`

This owner records the concrete characteristic-two polynomial only.  It does
not identify it with any G₂ peeling coordinate.
-/

namespace InfoGeometry.Physics.Algebra.ArtinSchreierF2

def artinSchreier (x : ZMod 2) : ZMod 2 := x ^ 2 - x

/-! In characteristic two the Artin--Schreier polynomial has the usual
`x^2 + x` presentation.  This is the concrete bridge used by the finite
peeling interpretation; no field-extension claim is made here. -/
theorem artinSchreier_eq_add (x : ZMod 2) :
    artinSchreier x = x ^ 2 + x := by
  fin_cases x <;> decide

def artinSchreierHom : ZMod 2 →+ ZMod 2 where
  toFun := artinSchreier
  map_zero' := by simp [artinSchreier]
  map_add' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide

theorem artinSchreier_eq_zero (x : ZMod 2) :
    artinSchreier x = 0 := by
  fin_cases x <;> decide

theorem artinSchreier_equation_exists_iff (a : ZMod 2) :
    (∃ x : ZMod 2, artinSchreier x = a) ↔ a = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    rw [artinSchreier_eq_zero x] at hx
    exact hx.symm
  · intro ha
    exact ⟨0, by simp [ha, artinSchreier]⟩

/-!
### Galois Field 𝔽₈ & Frobenius Fixed Points

The defining polynomial of 𝔽₈ as a cubic extension of 𝔽₂ is `x^8 = x` (Frobenius automorphism).
The nonzero elements form a multiplicative group of order 7, satisfying `x^7 = 1`.
The equation `x^7 = x` in 𝔽₈ only isolates the subfield 𝔽₂ = {0, 1}.
-/

section GaloisF8

variable {K : Type*} [Field K] [Fintype K]

/-- Frobenius fixed-point identity for any finite field of cardinality q: `x^q = x`. -/
theorem finite_field_card_power (x : K) :
    x ^ (Fintype.card K) = x :=
  FiniteField.pow_card x

/-- In a field with 8 elements, the defining Frobenius identity is `x^8 = x`. -/
theorem f8_defining_frobenius (hK : Fintype.card K = 8) (x : K) :
    x ^ 8 = x := by
  have h := FiniteField.pow_card (K := K) x
  rwa [hK] at h

/-- The multiplicative group of 𝔽₈ has exponent 7: every nonzero element satisfies `x^7 = 1`. -/
theorem f8_units_order_seven (hK : Fintype.card K = 8) (x : K) (hx : x ≠ 0) :
    x ^ 7 = 1 := by
  have h8 : x ^ 8 = x := f8_defining_frobenius hK x
  have h8_split : x ^ 7 * x = 1 * x := by
    calc
      x ^ 7 * x = x ^ (7 + 1) := (pow_succ x 7).symm
      _ = x ^ 8 := by rfl
      _ = x := h8
      _ = 1 * x := by rw [one_mul]
  exact mul_right_cancel₀ hx h8_split

/-- In 𝔽₈, the only solutions to `x^7 = x` are the base field elements {0, 1} = 𝔽₂. -/
theorem f8_seven_potent_is_f2 (hK : Fintype.card K = 8) (x : K) (h : x ^ 7 = x) :
    x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · left; exact hx
  · right
    have h7 : x ^ 7 = 1 := f8_units_order_seven hK x hx
    rw [h7] at h
    exact h.symm

end GaloisF8

end InfoGeometry.Physics.Algebra.ArtinSchreierF2
