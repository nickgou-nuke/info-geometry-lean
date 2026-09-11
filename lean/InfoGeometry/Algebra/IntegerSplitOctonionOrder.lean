import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Int.Basic

/-!
# Zorn Integer Order (Split Octonions over ℤ)

This file formalizes the naive integer ring of Zorn vector matrices,
which corresponds to the Lipschitz analogue for the split octonions $\mathbb{O}'(\mathbb{Z})_{\text{Zorn}}$.

It is a non-associative composition ring over the integers. While it is not the
true maximal order (the van der Blij-Springer $\mathcal{O}_{\text{split}}$ order
which requires half-integers to form the $E_{8(8)}$ lattice), it serves as the
foundational $\mathbb{Z}$-lattice from which the maximal order is constructed.
-/

namespace InfoGeometry.Algebra

/-- The naive integer Zorn matrix order (Lipschitz analogue).
    This forms a non-associative composition ring over ℤ. -/
abbrev ZornIntegerMatrix := ZornVectorMatrix ℤ

namespace ZornIntegerMatrix

/-- The norm of a Zorn integer matrix is strictly an integer. -/
theorem norm_is_int (X : ZornIntegerMatrix) : 
  ZornVectorMatrix.norm X = X.a * X.b - ZornVec3.dot X.v X.w := rfl

/-- The trace of a Zorn integer matrix is strictly an integer. -/
theorem trace_is_int (X : ZornIntegerMatrix) : 
  ZornVectorMatrix.trace X = X.a + X.b := rfl

/-- Norm multiplicativity for the integer Zorn matrices. 
    This establishes it as a composition algebra over ℤ. -/
theorem norm_mul (X Y : ZornIntegerMatrix) : 
  ZornVectorMatrix.norm (ZornVectorMatrix.mul X Y) = 
  ZornVectorMatrix.norm X * ZornVectorMatrix.norm Y := 
ZornVectorMatrix.norm_mul X Y

/-- The identity element has norm 1. -/
theorem norm_one : 
  ZornVectorMatrix.norm (ZornVectorMatrix.one : ZornIntegerMatrix) = 1 := by
  simp [ZornVectorMatrix.norm, ZornVectorMatrix.one, ZornVec3.dot]

/-- The zero element has norm 0. -/
theorem norm_zero : 
  ZornVectorMatrix.norm (ZornVectorMatrix.zero : ZornIntegerMatrix) = 0 := by
  simp [ZornVectorMatrix.norm, ZornVectorMatrix.zero, ZornVec3.dot]

/-- The norm form is a quadratic form over ℤ. 
    Here we demonstrate the scaling property. -/
theorem norm_smul (z : ℤ) (X : ZornIntegerMatrix) :
  ZornVectorMatrix.norm (ZornVectorMatrix.smul z X) = z^2 * ZornVectorMatrix.norm X := by
  simp [ZornVectorMatrix.norm, ZornVectorMatrix.smul, ZornVec3.dot_eq_sum_coords]
  ring

end ZornIntegerMatrix

end InfoGeometry.Algebra
