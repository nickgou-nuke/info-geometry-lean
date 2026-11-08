/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanGradedDifferential
import InfoGeometry.Algebra.PeirceLieJordanResolution
import InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution

/-! # Idempotent inner actions and quadratic conservation identities

The recurrence is an identity in an endomorphism ring, not a time-periodic
flow. Its quadratic generators are arbitrary noncommutative operators.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

open InfoGeometry.Core.PeirceDecomposition

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- The existing corner resolution identifies the actual squared endomorphism. -/
theorem peirce_lie_square {p : A} (hp : p * p = p) :
    lieOp R p * lieOp R p =
      PeirceLieJordanResolution.corner R p true false +
        PeirceLieJordanResolution.corner R p false true := by
  ext x
  change InfoGeometry.OperatorAlgebra.LieJordanDuality.ad R p
      (InfoGeometry.OperatorAlgebra.LieJordanDuality.ad R p x) = _
  rw [PeirceLieJordanResolution.ad_square_eq_oddPart R hp]
  rfl

/-- The inner action of an idempotent is tripotent. -/
theorem peirce_lie_cube {p : A} (hp : p * p = p) :
    lieOp R p * lieOp R p * lieOp R p = lieOp R p := by
  ext x
  change p * (p * (p * x - x * p) - (p * x - x * p) * p) -
    (p * (p * x - x * p) - (p * x - x * p) * p) * p = p * x - x * p
  noncomm_ring [hp, idempotent_mul_nested p hp]

theorem forward_from_inner_action {p : A} (hp : p * p = p) (a : A) :
    component10 p a = p * lieOp R p a := by
  simp only [component10, complementIdempotent, lieOp_apply]
  noncomm_ring [hp, idempotent_mul_nested p hp]

theorem reverse_from_inner_action {p : A} (hp : p * p = p) (a : A) :
    component01 p a = -(lieOp R p a * p) := by
  simp only [component01, complementIdempotent, lieOp_apply]
  noncomm_ring [hp, idempotent_mul_nested p hp]

/-- Leibniz on the actual inner-action endomorphism. -/
theorem lieOp_mul (p x y : A) :
    lieOp R p (x * y) = lieOp R p x * y + x * lieOp R p y := by
  simp only [lieOp_apply]
  noncomm_ring

/-- A reciprocal algebraic pair has this exact quadratic derivative. -/
theorem reciprocal_product_derivative {p j e : A}
    (hj : lieOp R p j = e) (he : lieOp R p e = j) :
    lieOp R p (j * e) = e * e + j * j := by
  rw [lieOp_mul, hj, he]

theorem reciprocal_square_derivative {p j e : A}
    (he : lieOp R p e = j) :
    lieOp R p (e * e) = jordanOp R j e := by
  rw [lieOp_mul, he]
  rfl

theorem reciprocal_product_stationary_iff {p j e : A}
    (hj : lieOp R p j = e) (he : lieOp R p e = j) :
    lieOp R p (j * e) = 0 ↔ e * e + j * j = 0 := by
  rw [reciprocal_product_derivative R hj he]

theorem reciprocal_square_stationary_iff {p j e : A}
    (he : lieOp R p e = j) :
    lieOp R p (e * e) = 0 ↔ jordanOp R j e = 0 := by
  rw [reciprocal_square_derivative R he]

section SquareZeroPair
variable {q r : A}

private theorem nilpotent_left (q : A) (hq : q * q = 0) (x : A) :
    q * (q * x) = 0 := by rw [← mul_assoc, hq, zero_mul]

/-- The symmetric product centralizes each generator, not the whole algebra. -/
theorem pair_square_commutes_left (hq : q * q = 0) :
    (q * r + r * q) * q = q * (q * r + r * q) := by
  noncomm_ring [hq, nilpotent_left q hq]

theorem pair_square_commutes_right (hr : r * r = 0) :
    (q * r + r * q) * r = r * (q * r + r * q) := by
  noncomm_ring [hr, nilpotent_left r hr]

/-- The two weighted commutators retain the nonscalar symmetric product. -/
theorem pair_commutator_on_sum (hq : q * q = 0) (hr : r * r = 0) :
    lieOp R (q * r - r * q) (q + r) =
      (2 : ℕ) • ((q * r + r * q) * (q - r)) := by
  simp only [lieOp_apply, two_nsmul]
  noncomm_ring [hq, hr, nilpotent_left q hq, nilpotent_left r hr]

theorem pair_commutator_on_difference (hq : q * q = 0) (hr : r * r = 0) :
    lieOp R (q * r - r * q) (q - r) =
      (2 : ℕ) • ((q * r + r * q) * (q + r)) := by
  simp only [lieOp_apply, two_nsmul]
  noncomm_ring [hq, hr, nilpotent_left q hq, nilpotent_left r hr]

/-- The symmetric product also centralizes the antisymmetric product. -/
theorem pair_quadratic_commute (hq : q * q = 0) (hr : r * r = 0) :
    (q * r + r * q) * (q * r - r * q) =
      (q * r - r * q) * (q * r + r * q) := by
  noncomm_ring [hq, hr, nilpotent_left q hq, nilpotent_left r hr]

end SquareZeroPair
end InfoGeometry.OperatorAlgebra.LieJordan
