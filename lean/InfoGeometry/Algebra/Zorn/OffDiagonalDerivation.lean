/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornVectorMatrix

/-! # Off-diagonal derivations for the existing Zorn product

The diagonal-to-vector terms have signs opposite to the proposed informal
formula. All identities use the actual nonassociative product, over any
commutative ring, including characteristics two and three.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-- The six-parameter off-diagonal action in the owner's sign convention. -/
def offDiagonalAction (p q : ZornVec3 R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  ⟨ZornVec3.dot p X.w - ZornVec3.dot q X.v,
   fun i => (X.b - X.a) * p i + ZornVec3.cross q X.w i,
   fun i => (X.a - X.b) * q i - ZornVec3.cross p X.v i,
   ZornVec3.dot q X.v - ZornVec3.dot p X.w⟩

theorem offDiagonalAction_leibniz (p q : ZornVec3 R)
    (X Y : ZornVectorMatrix R) :
    offDiagonalAction p q (mul X Y) =
      add (mul (offDiagonalAction p q X) Y) (mul X (offDiagonalAction p q Y)) := by
  ext i
  all_goals try fin_cases i
  all_goals simp [offDiagonalAction, mul, add, ZornVec3.dot,
    ZornVec3.cross, Fin.sum_univ_three]
  all_goals ring

/-- A genuine bundled linear Leibniz derivation, on the existing carrier. -/
def offDiagonalDerivation (p q : ZornVec3 R) : Derivation (R := R) where
  toFun := offDiagonalAction p q
  map_add' X Y := by
    ext i
    all_goals try fin_cases i
    all_goals simp [offDiagonalAction, add, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    all_goals ring
  map_smul' r X := by
    ext i
    all_goals try fin_cases i
    all_goals simp [offDiagonalAction, smul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    all_goals ring
  map_mul' := offDiagonalAction_leibniz p q

/-- The bracket formula holds on every input, with coefficient positive two. -/
theorem offDiagonalAction_upper_bracket (p r : ZornVec3 R)
    (X : ZornVectorMatrix R) :
    sub (offDiagonalAction p 0 (offDiagonalAction r 0 X))
      (offDiagonalAction r 0 (offDiagonalAction p 0 X)) =
      offDiagonalAction 0 (2 • ZornVec3.cross p r) X := by
  ext i
  all_goals try fin_cases i
  all_goals simp [offDiagonalAction, sub, add, neg, ZornVec3.dot,
    ZornVec3.cross, Fin.sum_univ_three, two_smul]
  all_goals ring

theorem offDiagonalDerivation_upper_bracket (p r : ZornVec3 R) :
    Derivation.bracket (offDiagonalDerivation p 0) (offDiagonalDerivation r 0) =
      offDiagonalDerivation 0 (2 • ZornVec3.cross p r) := by
  apply Derivation.ext
  intro X
  exact offDiagonalAction_upper_bracket p r X

@[simp] theorem trace_offDiagonalAction (p q : ZornVec3 R)
    (X : ZornVectorMatrix R) : trace (offDiagonalAction p q X) = 0 := by
  simp [trace, offDiagonalAction]

end InfoGeometry.Algebra.ZornVectorMatrix
