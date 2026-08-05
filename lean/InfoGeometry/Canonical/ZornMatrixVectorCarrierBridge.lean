import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Coordinate bridge between the two native Zorn carriers

`ZornMatrix` and the older `ZornVectorMatrix` use the same eight coordinates,
with the latter writing the diagonal as `(a,b)` and the off-diagonal entries
as `(v,w)`.  This owner proves the coordinate equivalence and its compatibility
with the two explicit Zorn products.  It does not install either product as an
associative matrix multiplication.
-/

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R]

def zornMatrixToVector
    (X : ZornMatrix R) : InfoGeometry.Algebra.ZornVectorMatrix R :=
  ⟨X.a, X.x, X.y, X.b⟩

def zornVectorToMatrix
    (X : InfoGeometry.Algebra.ZornVectorMatrix R) : ZornMatrix R :=
  ⟨X.a, X.b, X.v, X.w⟩

theorem zornVectorToMatrix_toVector (X : ZornMatrix R) :
    zornVectorToMatrix (zornMatrixToVector X) = X := by
  rfl

theorem zornMatrixToVector_toMatrix
    (X : InfoGeometry.Algebra.ZornVectorMatrix R) :
    zornMatrixToVector (zornVectorToMatrix X) = X := by
  rfl

theorem zornMatrixToVector_mul (X Y : ZornMatrix R) :
    zornMatrixToVector (ZornMatrix.mul X Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.mul
        (zornMatrixToVector X) (zornMatrixToVector Y) := by
  ext i
  · simp [zornMatrixToVector, ZornMatrix.mul,
      ZornMatrix.dot, ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVectorMatrix.mul,
      InfoGeometry.Algebra.ZornVec3.dot,
      InfoGeometry.Algebra.ZornVec3.cross, Fin.sum_univ_three]
  · fin_cases i <;>
      simp [zornMatrixToVector, ZornMatrix.mul,
        ZornMatrix.dot, ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVectorMatrix.mul,
      InfoGeometry.Algebra.ZornVec3.dot,
      InfoGeometry.Algebra.ZornVec3.cross, Fin.sum_univ_three,
      Pi.smul_apply, Matrix.vecHead, Matrix.vecTail] <;>
      ring
  · fin_cases i <;>
      simp [zornMatrixToVector, ZornMatrix.mul,
        ZornMatrix.dot, ZornMatrix.cross,
        InfoGeometry.Algebra.ZornVectorMatrix.mul,
        InfoGeometry.Algebra.ZornVec3.dot,
        InfoGeometry.Algebra.ZornVec3.cross, Fin.sum_univ_three,
        Pi.smul_apply, Matrix.vecHead, Matrix.vecTail] <;>
      ring
  · simp [zornMatrixToVector, ZornMatrix.mul,
      ZornMatrix.dot, ZornMatrix.cross,
      InfoGeometry.Algebra.ZornVectorMatrix.mul,
      InfoGeometry.Algebra.ZornVec3.dot,
      InfoGeometry.Algebra.ZornVec3.cross, Fin.sum_univ_three,
      Pi.smul_apply, Matrix.vecHead, Matrix.vecTail]
    ring

theorem zornMatrixToVector_add (X Y : ZornMatrix R) :
    zornMatrixToVector (X + Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.add
        (zornMatrixToVector X) (zornMatrixToVector Y) := by
  ext i <;> simp [zornMatrixToVector,
    InfoGeometry.Algebra.ZornVectorMatrix.add]

theorem zornMatrixToVector_sub (X Y : ZornMatrix R) :
    zornMatrixToVector (X - Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.sub
        (zornMatrixToVector X) (zornMatrixToVector Y) := by
  ext i <;> simp [zornMatrixToVector,
    InfoGeometry.Algebra.ZornVectorMatrix.sub,
    InfoGeometry.Algebra.ZornVectorMatrix.add,
    InfoGeometry.Algebra.ZornVectorMatrix.neg,
    sub_eq_add_neg]

end InfoGeometry.Canonical
