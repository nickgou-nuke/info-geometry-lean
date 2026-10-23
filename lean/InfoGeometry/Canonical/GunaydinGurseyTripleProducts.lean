/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GunaydinGurseyQuarkBasisBridge

/-! Parenthesized triple products in the existing signed Zorn basis.
The star in `uStar` is a basis label, not canonical Zorn conjugation.
These are nonassociative element identities, not a Lie superalgebra instance. -/
namespace InfoGeometry.Canonical.GunaydinGursey

open InfoGeometry.Algebra InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

theorem triple_left :
    mul (mul (u 0 : ZornVectorMatrix R) (u 1)) (u 2) = neg uStarZero := by
  unfold u uStarZero
  rw [V_zero_mul_V_one, ZornVectorMatrix.neg_mul, U_mul_V_self]

theorem triple_right :
    mul (u 0 : ZornVectorMatrix R) (mul (u 1) (u 2)) = neg uZero := by
  unfold u uZero
  rw [V_one_mul_V_two, ZornVectorMatrix.mul_neg, V_mul_U_self]

theorem triple_associator :
    associator (u 0 : ZornVectorMatrix R) (u 1) (u 2) =
      sub uZero uStarZero := by
  unfold associator
  rw [triple_left, triple_right]
  ext i <;> simp [sub, add, neg] <;> ring

theorem triple_jacobiator :
    commutatorJacobiator (u 0 : ZornVectorMatrix R) (u 1) (u 2) =
      smul (-6 : R) (sub uZero uStarZero) := by
  rw [u, u, u, commutator_jacobi_V_zero_V_one_V_two]
  ext i <;> simp [uZero, uStarZero, E11, E22, diagonal, smul, sub, add, neg]

end InfoGeometry.Canonical.GunaydinGursey
