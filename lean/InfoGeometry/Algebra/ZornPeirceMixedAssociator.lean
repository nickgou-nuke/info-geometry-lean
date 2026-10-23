/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornVectorMatrix

/-! Mixed Peirce associators on the existing nonassociative Zorn carrier. -/
namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-- Two upper vectors and one lower vector give the vector triple-product defect. -/
theorem associator_upper_upper_lower (u v w : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal v 0) (offDiagonal 0 w) =
      offDiagonal (fun i => ZornVec3.dot v w * u i - ZornVec3.dot u w * v i) 0 := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- Exact vanishing criterion, with no division or nondegeneracy assumptions. -/
theorem associator_upper_upper_lower_eq_zero_iff (u v w : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal v 0) (offDiagonal 0 w) = zero ↔
      ∀ i, ZornVec3.dot v w * u i = ZornVec3.dot u w * v i := by
  rw [associator_upper_upper_lower]
  constructor
  · intro h i
    have hi := congrArg (fun X : ZornVectorMatrix R => X.v i) h
    exact sub_eq_zero.mp hi
  · intro h
    ext i <;> simp [offDiagonal, zero, h]

/-- The mixed triple from the intake has zero associator; the three-upper
witness is already `associator_U_zero_U_one_U_two` in the native owner. -/
theorem associator_U_zero_U_one_V_two :
    associator (U 0 : ZornVectorMatrix R) (U 1) (V 2) = zero := by
  unfold associator
  rw [U_zero_mul_U_one, V_mul_self_zero, U_one_mul_V_two, mul_zero]
  ext i <;> simp [sub, add, neg, zero]

/-- Canonical conjugation exchanges the diagonal Peirce components. -/
theorem conj_diagonal (a b : R) :
    conj (diagonal a b : ZornVectorMatrix R) = diagonal b a := by
  ext i <;> simp [conj, diagonal]

end InfoGeometry.Algebra.ZornVectorMatrix
