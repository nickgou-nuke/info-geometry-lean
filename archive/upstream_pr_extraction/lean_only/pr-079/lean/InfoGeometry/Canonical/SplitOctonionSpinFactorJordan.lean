import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Symmetric Jordan structure of the split-octonion carrier

The symmetric part of the native Zorn product is recorded separately from
the Malcev commutator.  The carrier remains the explicit non-associative
Zorn structure; no associative multiplication is installed.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [Field R] [CharZero R]

def jordanProduct (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  smul (2 : R)⁻¹ (add (mul X Y) (mul Y X))

theorem jordanProduct_comm (X Y : ZornVectorMatrix R) :
    jordanProduct X Y = jordanProduct Y X := by
  unfold jordanProduct
  rw [add_comm]

theorem jordanProduct_one (X : ZornVectorMatrix R) :
    jordanProduct one X = X := by
  unfold jordanProduct
  rw [mul_one, one_mul]
  ext i <;> simp [smul, add, one] <;> ring

set_option maxHeartbeats 3000000 in
theorem jordan_identity (X Y : ZornVectorMatrix R) :
    jordanProduct X (jordanProduct Y (jordanProduct X X)) =
      jordanProduct (jordanProduct X Y) (jordanProduct X X) := by
  ext i
  · simp [jordanProduct, smul, add, neg, sub, mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [jordanProduct, smul, add, neg, sub, mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [jordanProduct, smul, add, neg, sub, mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [jordanProduct, smul, add, neg, sub, mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring

def gradingElement : ZornVectorMatrix R := diagonal 1 (-1)

theorem gradingElement_jordan_self :
    jordanProduct (gradingElement (R := R)) gradingElement = one := by
  ext i <;> simp [jordanProduct, gradingElement, diagonal, one, mul,
    smul, add, ZornVec3.dot, ZornVec3.cross] <;> ring

theorem gradingElement_jordan_offDiagonal (v w : ZornVec3 R) :
    jordanProduct (gradingElement (R := R)) (offDiagonal v w) =
      zero := by
  ext i <;> simp [jordanProduct, gradingElement, diagonal, offDiagonal,
    zero, mul, smul, add, ZornVec3.dot, ZornVec3.cross] <;> ring

end InfoGeometry.Algebra.ZornVectorMatrix
