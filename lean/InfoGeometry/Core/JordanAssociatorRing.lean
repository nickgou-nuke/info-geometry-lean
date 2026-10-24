/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing

/-!
# Unnormalized associative-envelope identities over rings

These identities use `x*y + y*x`, without division by two. The normalized
real-algebra Jordan product remains owned by `JordanPeirceDecomposition`.
No bundled Jordan or Kantor triple-system structure is asserted here.
-/
namespace InfoGeometry.Core.JordanAssociator

variable {R : Type*} [Ring R]

/-- Division-free recovery of the quadratic sandwich from symmetrized products. -/
theorem symm_quadratic_sandwich (x y : R) :
    ((x * y + y * x) * x + x * (x * y + y * x)) -
      ((x * x) * y + y * (x * x)) = 2 • (x * y * x) := by
  simp only [two_nsmul]
  noncomm_ring

/-- The three Jordan terms recover the symmetrized associative triple. -/
theorem symm_jordan_triple (x y z : R) :
    ((x * y + y * x) * z + z * (x * y + y * x)) +
      (x * (y * z + z * y) + (y * z + z * y) * x) -
      ((x * z + z * x) * y + y * (x * z + z * x)) =
        2 • (x * y * z + z * y * x) := by
  simp only [two_nsmul]
  noncomm_ring

/-- The unnormalized symmetrized-product associator is a double commutator. -/
theorem symm_associator_eq_double_commutator (x y z : R) :
    ((x * y + y * x) * z + z * (x * y + y * x)) -
      (x * (y * z + z * y) + (y * z + z * y) * x) =
        y * (x * z - z * x) - (x * z - z * x) * y := by
  noncomm_ring

/-- The correct triple expansion has a left multiplication by `z` in its correction. -/
theorem symm_triple_eq_symm_sub_commutator (x y z : R) :
    x * y * z + z * y * x =
      (x * y) * z + z * (x * y) - z * (x * y - y * x) := by
  noncomm_ring

/-- Exact obstruction to the alternate triple expansion proposed in the source note. -/
theorem proposed_triple_formula_defect (x y z : R) :
    ((x * y) * z + z * (x * y) - (x * (z * y) - (z * y) * x)) -
      (x * y * z + z * y * x) = (z * x - x * z) * y := by
  noncomm_ring

/-- Square-zero and an inner inverse suffice for the unnormalized `-2d` law;
neither an involution nor the other Moore–Penrose equations are needed. -/
theorem symm_associator_square_zero_inner_inverse {d b : R}
    (hd : d * d = 0) (hinner : d * b * d = d) :
    ((d * d + d * d) * b + b * (d * d + d * d)) -
      (d * (d * b + b * d) + (d * b + b * d) * d) = -(2 • d) := by
  rw [symm_associator_eq_double_commutator]
  calc
    _ = (d * d) * b - (d * b * d + d * b * d) + b * (d * d) := by
      noncomm_ring
    _ = -(2 • d) := by rw [hd, hinner]; simp [two_mul]

/-- For an idempotent, vanishing of the double commutator already detects
commutation. No characteristic restriction is required. -/
theorem idempotent_double_commutator_zero_iff {p q : R} (hp : p * p = p) :
    p * (p * q - q * p) - (p * q - q * p) * p = 0 ↔ p * q = q * p := by
  constructor
  · intro hz
    have hc : p * q - q * p = 0 := by
      calc
        p * q - q * p =
            p * (p * (p * q - q * p) - (p * q - q * p) * p) -
              (p * (p * q - q * p) - (p * q - q * p) * p) * p := by
                have hl (x : R) : p * (p * x) = p * x := by
                  rw [← mul_assoc, hp]
                noncomm_ring [hp]
                simp only [hl]
                abel
        _ = 0 := by rw [hz, mul_zero, zero_mul, sub_self]
    exact sub_eq_zero.mp hc
  · intro hc
    rw [hc, sub_self, mul_zero, zero_mul, sub_self]

/-- With one idempotent endpoint, vanishing of every middle-input
unnormalized Jordan associator is equivalent to commutation of the endpoints.
The other endpoint need not be idempotent. -/
theorem idempotent_all_associators_zero_iff {p q : R} (hp : p * p = p) :
    (∀ z : R,
      ((p * z + z * p) * q + q * (p * z + z * p)) -
        (p * (z * q + q * z) + (z * q + q * z) * p) = 0) ↔
      p * q = q * p := by
  simp only [symm_associator_eq_double_commutator]
  constructor
  · intro hz
    exact (idempotent_double_commutator_zero_iff hp).mp (hz p)
  · intro hc z
    rw [hc, sub_self, mul_zero, zero_mul, sub_self]

/-- Inner commutators differentiate the unnormalized Jordan product. -/
theorem commutator_symm_leibniz (l x y : R) :
    l * (x * y + y * x) - (x * y + y * x) * l =
      (l * x - x * l) * y + y * (l * x - x * l) +
        (x * (l * y - y * l) + (l * y - y * l) * x) := by
  noncomm_ring

/-- Composing two inner commutators gives their usual Lie bracket. -/
theorem commutator_operator_commutator (s t x : R) :
    (s * (t * x - x * t) - (t * x - x * t) * s) -
      (t * (s * x - x * s) - (s * x - x * s) * t) =
        (s * t - t * s) * x - x * (s * t - t * s) := by
  noncomm_ring

/-- The commutator of an inner derivation with Jordan multiplication. -/
theorem commutator_symm_operator (l t x : R) :
    (l * (t * x + x * t) - (t * x + x * t) * l) -
      (t * (l * x - x * l) + (l * x - x * l) * t) =
        (l * t - t * l) * x + x * (l * t - t * l) := by
  noncomm_ring

/-- The order is `[s,t]`, not `[t,s]`. This is an associative-envelope
identity, not an identification of an exceptional Lie algebra. -/
theorem symm_operator_commutator (s t x : R) :
    (s * (t * x + x * t) + (t * x + x * t) * s) -
      (t * (s * x + x * s) + (s * x + x * s) * t) =
        (s * t - t * s) * x - x * (s * t - t * s) := by
  noncomm_ring

/-- Exact obstruction to reversing the inner bracket in the Jordan-operator
commutator formula. The erroneous sign is invisible precisely when twice the
coefficient commutator commutes with the input, including characteristic two. -/
theorem symm_operator_reversed_bracket_iff (s t x : R) :
    ((s * (t * x + x * t) + (t * x + x * t) * s) -
      (t * (s * x + x * s) + (s * x + x * s) * t) =
        (t * s - s * t) * x - x * (t * s - s * t)) ↔
      Commute (2 • (s * t - t * s)) x := by
  rw [symm_operator_commutator]
  change _ = _ ↔ (2 • (s * t - t * s)) * x = x * (2 • (s * t - t * s))
  rw [← sub_eq_zero]
  have hdef :
      ((s * t - t * s) * x - x * (s * t - t * s)) -
        ((t * s - s * t) * x - x * (t * s - s * t)) =
      (2 • (s * t - t * s)) * x - x * (2 • (s * t - t * s)) := by
    simp only [two_nsmul]
    noncomm_ring
  rw [hdef, sub_eq_zero]

section Trace

variable {B : Type*} [AddCommGroup B] (τ : R →+ B)
    (hτ : ∀ x y : R, τ (x * y) = τ (y * x))

include hτ

/-- Cyclic additive maps annihilate inner commutators. -/
theorem trace_commutator (l x : R) : τ (l * x - x * l) = 0 := by
  rw [map_sub, hτ, sub_self]

/-- Infinitesimal invariance of the quadratic Jordan trace form. -/
theorem trace_symm_variation (l x y : R) :
    τ ((l * x - x * l) * y + y * (l * x - x * l) +
      (x * (l * y - y * l) + (l * y - y * l) * x)) = 0 := by
  rw [← commutator_symm_leibniz]
  exact trace_commutator τ hτ l _

/-- Infinitesimal invariance of the cubic Jordan trace expression.
This expression is not asserted to be a polarized determinant. -/
theorem trace_cubic_symm_variation (l x y z : R) :
    τ (((l * x - x * l) * y + y * (l * x - x * l)) * z +
      z * ((l * x - x * l) * y + y * (l * x - x * l)) +
      ((x * (l * y - y * l) + (l * y - y * l) * x) * z +
      z * (x * (l * y - y * l) + (l * y - y * l) * x)) +
      ((x * y + y * x) * (l * z - z * l) +
      (l * z - z * l) * (x * y + y * x))) = 0 := by
  have h : ((l * x - x * l) * y + y * (l * x - x * l)) * z +
      z * ((l * x - x * l) * y + y * (l * x - x * l)) +
      ((x * (l * y - y * l) + (l * y - y * l) * x) * z +
      z * (x * (l * y - y * l) + (l * y - y * l) * x)) +
      ((x * y + y * x) * (l * z - z * l) +
      (l * z - z * l) * (x * y + y * x)) =
      l * ((x * y + y * x) * z + z * (x * y + y * x)) -
      ((x * y + y * x) * z + z * (x * y + y * x)) * l := by
    noncomm_ring
  rw [h]
  exact trace_commutator τ hτ l _

/-- Exact linear trace variation under Jordan multiplication; no nonvanishing
claim is valid without further data. -/
theorem trace_symm (t x : R) : τ (t * x + x * t) = 2 • τ (t * x) := by
  rw [map_add, hτ x t, two_nsmul]

end Trace

end InfoGeometry.Core.JordanAssociator
