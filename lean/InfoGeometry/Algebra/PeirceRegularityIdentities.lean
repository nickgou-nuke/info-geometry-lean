/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.NoncommRing

/-!
# Associative identities underlying Peirce corners and regularity defects

All products are the actual products of an arbitrary associative ring.
The symmetrized product is unnormalized: `x*y + y*x`. No alternative Lie,
Jordan, inverse, or matrix carrier is introduced. The symmetrized triple
identities below do not assert a bundled Kantor triple-system construction.
-/
namespace InfoGeometry.Algebra.PeirceRegularityIdentities

variable {R : Type*} [Ring R]

/-- Orthogonality in the middle makes an off-diagonal corner square-zero. -/
theorem corner_square_zero (e f x : R) (hfe : f * e = 0) :
    (e * x * f) * (e * x * f) = 0 := by
  calc
    (e * x * f) * (e * x * f) = e * x * (f * e) * x * f := by
      simp only [mul_assoc]
    _ = 0 := by rw [hfe]; simp

/-- The four-corner expansion only requires that the two elements sum to one. -/
theorem two_corner_expansion (e f x : R) (hef : e + f = 1) :
    e * x * e + e * x * f + f * x * e + f * x * f = x := by
  calc
    _ = (e + f) * x * (e + f) := by noncomm_ring
    _ = x := by rw [hef]; simp

/-- Associator of the unnormalized symmetrized product is a double commutator. -/
theorem symm_associator_eq_double_commutator (x y z : R) :
    ((x * y + y * x) * z + z * (x * y + y * x)) -
      (x * (y * z + z * y) + (y * z + z * y) * x) =
        y * (x * z - z * x) - (x * z - z * x) * y := by
  noncomm_ring

/-- Correct triple-product decomposition; the correction multiplies on the left by z. -/
theorem symm_triple_eq_symm_sub_commutator (x y z : R) :
    x * y * z + z * y * x =
      (x * y) * z + z * (x * y) - z * (x * y - y * x) := by
  noncomm_ring

/-- Exact residual of the different triple-product identity in the source note. -/
theorem proposed_triple_formula_defect (x y z : R) :
    ((x * y) * z + z * (x * y) - (x * (z * y) - (z * y) * x)) -
      (x * y * z + z * y * x) = (z * x - x * z) * y := by
  noncomm_ring

/-- Symmetric support overlap, with no commutativity or characteristic assumption. -/
theorem idempotent_overlap_defect {p q : R}
    (hp : p * p = p) (hq : q * q = q) :
    (p + q) - (p - q) * (p - q) = p * q + q * p := by
  noncomm_ring [hp, hq]

/-- Difference of mutually annihilating idempotents is tripotent. -/
theorem orthogonal_difference_cube {p q : R}
    (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = 0) (hqp : q * p = 0) :
    (p - q) * (p - q) * (p - q) = p - q := by
  have hs : (p - q) * (p - q) = p + q := by
    noncomm_ring [hp, hq, hpq, hqp]
  rw [hs]
  noncomm_ring [hp, hq, hpq, hqp]

end InfoGeometry.Algebra.PeirceRegularityIdentities
