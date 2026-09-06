import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.WeylA1Character

Finite rank-one Weyl character identity.

This file does not attempt to formalize the full Weyl character formula for an
arbitrary root system. It records the honest `A1` / `SU(2)` geometric-series
identity behind the character computation:

* a finite alternating sum of weights `x^i y^(m-i)`;
* the denominator factor `x - y`;
* the cancellation identity

  `(\sum_{i=0}^m x^i y^(m-i)) * (x - y) = x^(m+1) - y^(m+1)`.

The `SU(2)` specialization is obtained by taking `y = x⁻¹`.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.WeylA1Character

/-- The finite `A1` character numerator. -/
@[rep_depth thermo]
def a1CharacterSum {R : Type*} [Semiring R] (x y : R) (m : ℕ) : R :=
  Finset.sum (Finset.range (m + 1)) (fun i => x ^ i * y ^ (m - i))

/-- The `A1` denominator factor `x - y`. -/
@[rep_depth thermo]
def a1Denominator {R : Type*} [Ring R] (x y : R) : R :=
  x - y

/-- Finite `A1` numerator/denominator cancellation. -/
@[rep_depth thermo]
theorem a1CharacterSum_mul_denominator
    {R : Type*} [CommRing R]
    (x y : R) (m : ℕ) :
    a1CharacterSum x y m * a1Denominator x y =
      x ^ (m + 1) - y ^ (m + 1) := by
  simpa [a1CharacterSum, a1Denominator, Nat.succ_eq_add_one,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (geom_sum₂_mul x y (m + 1))

/-- Finite `A1` numerator as a quotient by the denominator factor. -/
@[rep_depth thermo]
theorem a1CharacterSum_eq_div
    {R : Type*} [Field R]
    (x y : R) (m : ℕ) (hxy : x ≠ y) :
    a1CharacterSum x y m =
      (x ^ (m + 1) - y ^ (m + 1)) / (x - y) := by
  rw [eq_div_iff (sub_ne_zero.mpr hxy)]
  exact a1CharacterSum_mul_denominator (R := R) x y m

/-- The `SU(2)` specialization: `y = x⁻¹`. -/
@[rep_depth thermo]
def su2Character {R : Type*} [DivisionRing R] (x : R) (m : ℕ) : R :=
  a1CharacterSum x x⁻¹ m

/-- The `SU(2)` character multiplied by its denominator factor. -/
@[rep_depth thermo]
theorem su2Character_mul_denominator
    {R : Type*} [Field R]
    (x : R) (m : ℕ) :
    su2Character x m * a1Denominator x x⁻¹ =
      x ^ (m + 1) - (x ^ (m + 1))⁻¹ := by
  simpa [su2Character, a1Denominator, inv_pow] using
    (a1CharacterSum_mul_denominator (R := R) x x⁻¹ m)

/-- `SU(2)` character written as the Weyl-type quotient. -/
@[rep_depth thermo]
theorem su2Character_eq_div
    {R : Type*} [Field R]
    (x : R) (m : ℕ) (hx : x ≠ x⁻¹) :
    su2Character x m =
      (x ^ (m + 1) - (x ^ (m + 1))⁻¹) / (x - x⁻¹) := by
  simpa [su2Character, a1Denominator, inv_pow] using
    (a1CharacterSum_eq_div (R := R) x x⁻¹ m hx)

/-- The `SU(2)` character as a finite alternating weight sum. -/
@[simp, rep_depth thermo]
theorem su2Character_eq_sum
    {R : Type*} [Field R]
    (x : R) (m : ℕ) :
    su2Character x m = a1CharacterSum x x⁻¹ m := rfl

end InfoGeometry.Canonical.WeylA1Character
