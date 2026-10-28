/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceLieJordanResolution

/-!
# Joint Lie--Jordan eigenvalues of the actual Peirce projections

The eigenvalues are read from the two endpoint indices. No diagonalization or
commutation assumption on the observable is used. The cubic polynomial for the
adjoint follows from the already proved composition table, in any characteristic.
-/

namespace InfoGeometry.Algebra.PeirceLieJordanEigen

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Algebra.PeirceLieJordanResolution
open InfoGeometry.Core.JordanMultiplicationClosure

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

lemma left_corner {p : A} (hp : p * p = p) (i j : Bool) (x : A) :
    p * cornerOp (R := R) p i j x =
      if i then cornerOp (R := R) p i j x else 0 := by
  have he : p * endpoint p i = if i then p else 0 := by
    cases i <;> simp [endpoint, compIdempotent, mul_sub, hp]
  change p * (endpoint p i * x * endpoint p j) = _
  calc
    _ = (p * endpoint p i) * x * endpoint p j := by simp only [mul_assoc]
    _ = _ := by rw [he]; cases i <;> simp [cornerOp, endpoint]

lemma right_corner {p : A} (hp : p * p = p) (i j : Bool) (x : A) :
    cornerOp (R := R) p i j x * p =
      if j then cornerOp (R := R) p i j x else 0 := by
  have he : endpoint p j * p = if j then p else 0 := by
    cases j <;> simp [endpoint, compIdempotent, sub_mul, hp]
  change (endpoint p i * x * endpoint p j) * p = _
  calc
    _ = (endpoint p i * x) * (endpoint p j * p) := by simp only [mul_assoc]
    _ = _ := by rw [he]; cases j <;> simp [cornerOp, endpoint]

/-- Weights `0,0,1,-1` on the `11,00,10,01` corners. -/
theorem ad_corner {p : A} (hp : p * p = p) (i j : Bool) (x : A) :
    LieAlgebra.ad R A p (cornerOp (R := R) p i j x) =
      ((if i then (1 : ℤ) else 0) - (if j then 1 else 0)) •
        cornerOp (R := R) p i j x := by
  change p * cornerOp (R := R) p i j x - cornerOp (R := R) p i j x * p = _
  rw [left_corner hp, right_corner hp]
  cases i <;> cases j <;> simp

/-- Weights `2,0,1,1` on the same four full operator corners. -/
theorem jordan_corner {p : A} (hp : p * p = p) (i j : Bool) (x : A) :
    jordanLeft (R := R) p (cornerOp (R := R) p i j x) =
      ((if i then (1 : ℤ) else 0) + (if j then 1 else 0)) •
        cornerOp (R := R) p i j x := by
  change p * cornerOp (R := R) p i j x + cornerOp (R := R) p i j x * p = _
  rw [left_corner hp, right_corner hp]
  cases i <;> cases j <;> simp [two_mul]

/-- The adjoint action is the difference of the two off-diagonal projectors. -/
theorem ad_eq_corner_difference (p : A) :
    LieAlgebra.ad R A p =
      cornerOp (R := R) p true false - cornerOp (R := R) p false true := by
  ext x
  change p * x - x * p = p * x * (1 - p) - (1 - p) * x * p
  noncomm_ring

/-- An operator polynomial identity, not an assumed spectral decomposition. -/
theorem ad_cubic {p : A} (hp : p * p = p) :
    LieAlgebra.ad R A p * LieAlgebra.ad R A p * LieAlgebra.ad R A p =
      LieAlgebra.ad R A p := by
  simp only [ad_eq_corner_difference, sub_mul, mul_sub]
  simp [cornerOp_comp hp]

end InfoGeometry.Algebra.PeirceLieJordanEigen
