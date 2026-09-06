import InfoGeometry.OperatorAlgebra.GenericZorn
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Coordinate soldering between the two native split-octonion carriers

`GenericZorn.ZornSplitOctonion R` stores the eight coordinates explicitly,
while `ZornVectorMatrix R` stores the same data as two scalars and two
three-vectors.  This file proves that the two presentations are equivalent,
including transport of the explicit nonassociative product, norm, and
conjugation.  It does not turn the product into associative matrix
multiplication.
-/

namespace InfoGeometry.Algebra.ZornSplitOctonionVectorMatrixEquiv

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.OperatorAlgebra.GenericZorn

variable {R : Type*} [CommRing R]

/-- Pack eight scalar coordinates into the vector-matrix Zorn carrier. -/
def toVectorMatrix (X : ZornSplitOctonion R) : ZornVectorMatrix R :=
  ⟨X.a, fun i => ![X.x0, X.x1, X.x2] i,
    fun i => ![X.y0, X.y1, X.y2] i, X.b⟩

/-- Read the two three-vector blocks back as eight scalar coordinates. -/
def fromVectorMatrix (X : ZornVectorMatrix R) : ZornSplitOctonion R :=
  ⟨X.a, X.b, X.v 0, X.v 1, X.v 2, X.w 0, X.w 1, X.w 2⟩

@[simp] theorem from_to (X : ZornSplitOctonion R) :
    fromVectorMatrix (toVectorMatrix X) = X := by
  cases X
  rfl

@[simp] theorem to_from (X : ZornVectorMatrix R) :
    toVectorMatrix (fromVectorMatrix X) = X := by
  cases X with
  | mk a v w b =>
    apply ZornVectorMatrix.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl

/-- The coordinate soldering equivalence. -/
def equiv : ZornSplitOctonion R ≃ ZornVectorMatrix R where
  toFun := toVectorMatrix
  invFun := fromVectorMatrix
  left_inv := from_to
  right_inv := to_from

theorem toVectorMatrix_mul (X Y : ZornSplitOctonion R) :
    toVectorMatrix (mul X Y) =
      ZornVectorMatrix.mul (toVectorMatrix X) (toVectorMatrix Y) := by
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases Y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      apply ZornVectorMatrix.ext
      · simp [toVectorMatrix, InfoGeometry.OperatorAlgebra.GenericZorn.mul,
          ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
      · funext i
        fin_cases i <;>
          simp [toVectorMatrix, InfoGeometry.OperatorAlgebra.GenericZorn.mul,
            ZornVectorMatrix.mul, ZornVec3.cross]
      · funext i
        fin_cases i <;>
          simp [toVectorMatrix, InfoGeometry.OperatorAlgebra.GenericZorn.mul,
            ZornVectorMatrix.mul, ZornVec3.cross]
        all_goals ring
      · simp [toVectorMatrix, InfoGeometry.OperatorAlgebra.GenericZorn.mul,
          ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
        ring

theorem fromVectorMatrix_mul (X Y : ZornVectorMatrix R) :
    fromVectorMatrix (ZornVectorMatrix.mul X Y) =
      mul (fromVectorMatrix X) (fromVectorMatrix Y) := by
  cases X with
  | mk a v w b =>
    cases Y with
    | mk c u z d =>
      ext <;>
        simp [fromVectorMatrix,
          InfoGeometry.OperatorAlgebra.GenericZorn.mul,
          ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
          Fin.sum_univ_three]
      <;> ring

theorem toVectorMatrix_norm (X : ZornSplitOctonion R) :
    ZornVectorMatrix.norm (toVectorMatrix X) =
      InfoGeometry.OperatorAlgebra.GenericZorn.norm X := by
  cases X
  simp [toVectorMatrix, ZornVectorMatrix.norm,
    InfoGeometry.OperatorAlgebra.GenericZorn.norm,
    ZornVec3.dot, Fin.sum_univ_three]

theorem fromVectorMatrix_norm (X : ZornVectorMatrix R) :
    norm (fromVectorMatrix X) = ZornVectorMatrix.norm X := by
  rw [← toVectorMatrix_norm (fromVectorMatrix X)]
  simp

theorem toVectorMatrix_conjugate (X : ZornSplitOctonion R) :
    toVectorMatrix (conjugate X) = ZornVectorMatrix.conj (toVectorMatrix X) := by
  cases X
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem fromVectorMatrix_conjugate (X : ZornVectorMatrix R) :
    fromVectorMatrix (ZornVectorMatrix.conj X) = conjugate (fromVectorMatrix X) := by
  cases X with
  | mk a v w b =>
    apply ZornSplitOctonion.ext <;>
      simp [fromVectorMatrix, ZornVectorMatrix.conj,
        InfoGeometry.OperatorAlgebra.GenericZorn.conjugate]

end InfoGeometry.Algebra.ZornSplitOctonionVectorMatrixEquiv
