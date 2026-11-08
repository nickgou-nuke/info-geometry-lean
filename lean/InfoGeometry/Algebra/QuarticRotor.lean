/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Quartic rotor numerators in an associative ring

An eighth-root relation `ζ ^ 4 = -1` and a commuting fourth-root relation
`X ^ 4 = 1` give two polynomial numerators whose products, in both orders,
equal `4`. The ambient ring need not be commutative. The Gaussian sums and
parity-channel cancellation are proved separately as reusable identities.

The ring-level results do not assert a braid relation, an adjoint, or
unitarity. The star section identifies the second numerator with the star
of the first only under explicit star hypotheses. When `2` is invertible,
the normalized expression is constructed as an element of Mathlib's native
`unitary B`.
-/

namespace InfoGeometry.Algebra.QuarticRotor

variable {B : Type*} [Ring B]

/-- Polynomial numerator of the quartic rotor. -/
def rotorNumerator (ζ X : B) : B :=
  (1 - X ^ 2) + ζ * X * (1 + X ^ 2)

/-- Polynomial numerator paired with `rotorNumerator`. -/
def inverseNumerator (ζ X : B) : B :=
  (1 - X ^ 2) - ζ ^ 3 * X ^ 3 * (1 + X ^ 2)

/-- The fourth-power relation implies the eighth-power relation, in every
characteristic. It does not by itself imply exact multiplicative order eight. -/
theorem pow_eight_eq_one (ζ : B) (hζ4 : ζ ^ 4 = -1) : ζ ^ 8 = 1 := by
  calc
    ζ ^ 8 = (ζ ^ 4) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [hζ4]; simp

/-- The quadratic Gaussian identity for the internal square root of `-1`. -/
theorem quadratic_gauss_identity (ζ : B) (hζ4 : ζ ^ 4 = -1) :
    (1 + ζ ^ 2) ^ 2 = 2 * ζ ^ 2 := by
  calc
    (1 + ζ ^ 2) ^ 2 = 1 + 2 * ζ ^ 2 + ζ ^ 4 := by noncomm_ring
    _ = 2 * ζ ^ 2 := by rw [hζ4]; noncomm_ring

/-- The four-term Gaussian sum with square exponents `0, 1, 4, 9`. -/
theorem quartic_gauss_sum (ζ : B) (hζ4 : ζ ^ 4 = -1) :
    1 + ζ + ζ ^ 4 + ζ ^ 9 = 2 * ζ := by
  have hζ9 : ζ ^ 9 = ζ := by
    calc
      ζ ^ 9 = ζ ^ 8 * ζ := by rw [pow_succ]
      _ = ζ := by rw [pow_eight_eq_one ζ hζ4, one_mul]
  rw [hζ4, hζ9]
  noncomm_ring

/-- The two unnormalized parity factors annihilate each other. -/
theorem parity_factors_mul_zero (X : B) (hX4 : X ^ 4 = 1) :
    (1 - X ^ 2) * (1 + X ^ 2) = 0 := by
  calc
    (1 - X ^ 2) * (1 + X ^ 2) = 1 - X ^ 4 := by noncomm_ring
    _ = 0 := by rw [hX4, sub_self]

/-- Local commutation suffices to cancel the mixed parity channel. -/
theorem parity_channel_mul_zero (ζ X : B) (hX4 : X ^ 4 = 1)
    (hComm : Commute ζ X) :
    (1 - X ^ 2) * (ζ * X * (1 + X ^ 2)) = 0 := by
  have hmove (y : B) : X * (ζ * y) = ζ * (X * y) := by
    rw [← mul_assoc, hComm.eq.symm, mul_assoc]
  calc
    (1 - X ^ 2) * (ζ * X * (1 + X ^ 2)) =
        ζ * X * (1 - X ^ 4) := by
      noncomm_ring [hComm.eq.symm, hmove]
    _ = 0 := by rw [hX4]; simp

/-- The paired numerators commute because they are polynomials in the same
two commuting elements; no commutativity of the ambient ring is required. -/
theorem rotorNumerator_commute_inverseNumerator (ζ X : B)
    (hComm : Commute ζ X) :
    Commute (rotorNumerator ζ X) (inverseNumerator ζ X) := by
  have hmove (y : B) : X * (ζ * y) = ζ * (X * y) := by
    rw [← mul_assoc, hComm.eq.symm, mul_assoc]
  change rotorNumerator ζ X * inverseNumerator ζ X =
    inverseNumerator ζ X * rotorNumerator ζ X
  dsimp only [rotorNumerator, inverseNumerator]
  noncomm_ring [hComm.eq.symm, hmove]

/-- The division-free forward product of the paired rotor numerators. -/
theorem rotorNumerator_mul_inverseNumerator (ζ X : B)
    (hζ4 : ζ ^ 4 = -1) (hX4 : X ^ 4 = 1) (hComm : Commute ζ X) :
    rotorNumerator ζ X * inverseNumerator ζ X = 4 := by
  have hmove (y : B) : X * (ζ * y) = ζ * (X * y) := by
    rw [← mul_assoc, hComm.eq.symm, mul_assoc]
  calc
    rotorNumerator ζ X * inverseNumerator ζ X =
        (1 - X ^ 2 - X ^ 2 + X ^ 4) +
          (1 - X ^ 4) * (ζ * X - ζ ^ 3 * X ^ 3) -
          ζ ^ 4 * X ^ 4 * (1 + X ^ 2 + X ^ 2 + X ^ 4) := by
      dsimp only [rotorNumerator, inverseNumerator]
      noncomm_ring [hComm.eq.symm, hmove]
    _ = 4 := by rw [hζ4, hX4]; noncomm_ring; simp

/-- The reverse product is also `4`; the forward identity alone would not
justify treating the paired expression as a two-sided inverse. -/
theorem inverseNumerator_mul_rotorNumerator (ζ X : B)
    (hζ4 : ζ ^ 4 = -1) (hX4 : X ^ 4 = 1) (hComm : Commute ζ X) :
    inverseNumerator ζ X * rotorNumerator ζ X = 4 := by
  rw [← (rotorNumerator_commute_inverseNumerator ζ X hComm).eq]
  exact rotorNumerator_mul_inverseNumerator ζ X hζ4 hX4 hComm

section Star

variable [StarRing B]

/-- Under the stated inverse-star laws for the two generators, the paired
numerator is the actual star of the rotor numerator. -/
theorem star_rotorNumerator (ζ X : B) (hX4 : X ^ 4 = 1)
    (hComm : Commute ζ X) (hζstar : star ζ = -ζ ^ 3)
    (hXstar : star X = X ^ 3) :
    star (rotorNumerator ζ X) = inverseNumerator ζ X := by
  have hmove (y : B) : X * (ζ * y) = ζ * (X * y) := by
    rw [← mul_assoc, hComm.eq.symm, mul_assoc]
  have hX6 : (X ^ 3) ^ 2 = X ^ 2 := by
    calc
      (X ^ 3) ^ 2 = X ^ 4 * X ^ 2 := by noncomm_ring
      _ = X ^ 2 := by rw [hX4, one_mul]
  simp only [rotorNumerator, inverseNumerator, star_add, star_sub, star_mul,
    star_one, star_pow, hζstar, hXstar, hX6]
  noncomm_ring [hComm.eq.symm, hmove]

/-- A scaled star-norm identity. No division by `2` is used. -/
theorem rotorNumerator_mul_star (ζ X : B)
    (hζ4 : ζ ^ 4 = -1) (hX4 : X ^ 4 = 1) (hComm : Commute ζ X)
    (hζstar : star ζ = -ζ ^ 3) (hXstar : star X = X ^ 3) :
    rotorNumerator ζ X * star (rotorNumerator ζ X) = 4 := by
  rw [star_rotorNumerator ζ X hX4 hComm hζstar hXstar]
  exact rotorNumerator_mul_inverseNumerator ζ X hζ4 hX4 hComm

/-- The scaled star-norm identity in the other multiplication order. -/
theorem star_mul_rotorNumerator (ζ X : B)
    (hζ4 : ζ ^ 4 = -1) (hX4 : X ^ 4 = 1) (hComm : Commute ζ X)
    (hζstar : star ζ = -ζ ^ 3) (hXstar : star X = X ^ 3) :
    star (rotorNumerator ζ X) * rotorNumerator ζ X = 4 := by
  rw [star_rotorNumerator ζ X hX4 hComm hζstar hXstar]
  exact inverseNumerator_mul_rotorNumerator ζ X hζ4 hX4 hComm

section Normalized

variable [Invertible (2 : B)]

/-- The normalized rotor, using the inverse of the central element `2`. -/
def normalizedRotor (ζ X : B) : B :=
  ⅟(2 : B) * rotorNumerator ζ X

/-- The star of the normalized rotor is the normalized paired numerator.
The inverse of `2` is self-adjoint and commutes with every ring element. -/
theorem star_normalizedRotor (ζ X : B) (hX4 : X ^ 4 = 1)
    (hComm : Commute ζ X) (hζstar : star ζ = -ζ ^ 3)
    (hXstar : star X = X ^ 3) :
    star (normalizedRotor ζ X) = ⅟(2 : B) * inverseNumerator ζ X := by
  have hhalf : IsSelfAdjoint (⅟(2 : B)) := (IsSelfAdjoint.ofNat 2).invOf
  rw [normalizedRotor, star_mul, hhalf.star_eq,
    star_rotorNumerator ζ X hX4 hComm hζstar hXstar]
  exact (Commute.invOf_left ((2 : ℕ).cast_commute (inverseNumerator ζ X))).eq.symm

/-- Genuine unitarity after normalization. Only `2` must be invertible;
the ambient star ring need not be a field or be commutative. -/
theorem normalizedRotor_mem_unitary (ζ X : B)
    (hζ4 : ζ ^ 4 = -1) (hX4 : X ^ 4 = 1) (hComm : Commute ζ X)
    (hζstar : star ζ = -ζ ^ 3) (hXstar : star X = X ^ 3) :
    normalizedRotor ζ X ∈ unitary B := by
  have hproduct (a b : B) (hab : a * b = 4) :
      (⅟(2 : B) * a) * (⅟(2 : B) * b) = 1 := by
    have hhalf : Commute (⅟(2 : B)) a :=
      Commute.invOf_left ((2 : ℕ).cast_commute a)
    calc
      (⅟(2 : B) * a) * (⅟(2 : B) * b) =
          ⅟(2 : B) * (a * ⅟(2 : B)) * b := by simp only [mul_assoc]
      _ = ⅟(2 : B) * (⅟(2 : B) * a) * b := by rw [← hhalf.eq]
      _ = ⅟(2 : B) * ⅟(2 : B) * (a * b) := by simp only [mul_assoc]
      _ = ⅟(2 : B) * ⅟(2 : B) * 4 := by rw [hab]
      _ = ⅟(2 : B) * (⅟(2 : B) * 2) * 2 := by
        rw [show (4 : B) = 2 * 2 by norm_num]
        simp only [mul_assoc]
      _ = 1 := by rw [invOf_mul_self, mul_one, invOf_mul_self]
  constructor
  · rw [star_normalizedRotor ζ X hX4 hComm hζstar hXstar]
    exact hproduct (inverseNumerator ζ X) (rotorNumerator ζ X)
      (inverseNumerator_mul_rotorNumerator ζ X hζ4 hX4 hComm)
  · rw [star_normalizedRotor ζ X hX4 hComm hζstar hXstar]
    exact hproduct (rotorNumerator ζ X) (inverseNumerator ζ X)
      (rotorNumerator_mul_inverseNumerator ζ X hζ4 hX4 hComm)

/-- The normalized quartic rotor as an element of the native unitary group. -/
def rotorUnitary (ζ X : B)
    (hζ4 : ζ ^ 4 = -1) (hX4 : X ^ 4 = 1) (hComm : Commute ζ X)
    (hζstar : star ζ = -ζ ^ 3) (hXstar : star X = X ^ 3) : unitary B :=
  ⟨normalizedRotor ζ X,
    normalizedRotor_mem_unitary ζ X hζ4 hX4 hComm hζstar hXstar⟩

@[simp]
theorem coe_rotorUnitary (ζ X : B)
    (hζ4 : ζ ^ 4 = -1) (hX4 : X ^ 4 = 1) (hComm : Commute ζ X)
    (hζstar : star ζ = -ζ ^ 3) (hXstar : star X = X ^ 3) :
    (rotorUnitary ζ X hζ4 hX4 hComm hζstar hXstar : B) =
      ⅟(2 : B) * rotorNumerator ζ X := rfl

end Normalized

end Star

end InfoGeometry.Algebra.QuarticRotor
