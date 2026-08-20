import Mathlib
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Square readout for an off-diagonal Zorn field

This owner proves the finite Zorn-product square used as an invariant readout.
It does not introduce eigenvalues: non-associativity means that a standard
characteristic-polynomial interpretation requires a separate associative
representation.
-/

namespace InfoGeometry.Canonical.ZornMaxwellSquareReadout

open InfoGeometry.Algebra

abbrev RealVec3 := ZornVec3 ℝ
abbrev ZornMatrix := ZornVectorMatrix ℝ

theorem offDiagonal_mul_self (u v : RealVec3) :
    ZornVectorMatrix.mul (ZornVectorMatrix.offDiagonal u v)
      (ZornVectorMatrix.offDiagonal u v) =
      ZornVectorMatrix.diagonal (ZornVec3.dot u v) (ZornVec3.dot u v) := by
  ext i <;>
    simp [ZornVectorMatrix.mul, ZornVectorMatrix.offDiagonal,
      ZornVectorMatrix.diagonal, ZornVec3.cross_self, ZornVec3.dot_comm]

def electromagneticOffDiagonal (e b : RealVec3) : ZornMatrix :=
  ZornVectorMatrix.offDiagonal
    (fun i => -(e i + b i))
    (fun i => e i - b i)

theorem electromagnetic_scalar_invariant (e b : RealVec3) :
    ZornVec3.dot (fun i => -(e i + b i)) (fun i => e i - b i) =
      ZornVec3.dot b b - ZornVec3.dot e e := by
  simp [ZornVec3.dot, Fin.sum_univ_three]
  ring

theorem electromagneticOffDiagonal_square (e b : RealVec3) :
    ZornVectorMatrix.mul (electromagneticOffDiagonal e b)
      (electromagneticOffDiagonal e b) =
      ZornVectorMatrix.diagonal
        (ZornVec3.dot b b - ZornVec3.dot e e)
        (ZornVec3.dot b b - ZornVec3.dot e e) := by
  rw [electromagneticOffDiagonal, offDiagonal_mul_self]
  rw [electromagnetic_scalar_invariant]

theorem electromagneticOffDiagonal_square_eq_zero_of_null
    (e b : RealVec3)
    (hNull : ZornVec3.dot b b = ZornVec3.dot e e) :
    ZornVectorMatrix.mul (electromagneticOffDiagonal e b)
      (electromagneticOffDiagonal e b) = ZornVectorMatrix.zero := by
  rw [electromagneticOffDiagonal_square]
  rw [hNull, sub_self]
  rfl

theorem electromagneticOffDiagonal_norm (e b : RealVec3) :
    ZornVectorMatrix.norm (electromagneticOffDiagonal e b) =
      ZornVec3.dot e e - ZornVec3.dot b b := by
  simp [electromagneticOffDiagonal, ZornVectorMatrix.norm,
    ZornVectorMatrix.offDiagonal, ZornVec3.dot, Fin.sum_univ_three]
  ring

end InfoGeometry.Canonical.ZornMaxwellSquareReadout
