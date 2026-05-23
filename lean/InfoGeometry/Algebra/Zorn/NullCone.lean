import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# InfoGeometry.Algebra.Zorn.NullCone

This file re-exports the canonical square-zero readouts of the explicit Zorn
carrier.

It is the algebraic null-cone lane for the split-octonion shadow:
upper and lower off-diagonal vectors square to zero, and their mixed products
land in the diagonal sector.
-/

namespace InfoGeometry.Algebra.Zorn

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

abbrev Vec3 := InfoGeometry.Canonical.ZornVectorMatrixExplicit.Vec3
abbrev ZornCoord := InfoGeometry.Canonical.ZornVectorMatrixExplicit.ZornCoord

@[simp] theorem upperVector_square_zero (x : Vec3) :
    zornMul (upperVectorZorn x) (upperVectorZorn x) = 0 := by
  simpa using upperVectorZorn_square_zero x

@[simp] theorem lowerVector_square_zero (y : Vec3) :
    zornMul (lowerVectorZorn y) (lowerVectorZorn y) = 0 := by
  simpa using lowerVectorZorn_square_zero y

@[simp] theorem upper_lower_mul_diag (x y : Vec3) :
    zornMul (upperVectorZorn x) (lowerVectorZorn y) =
      zornMk (dot3 x y) 0 0 0 := by
  simpa using upperVectorZorn_mul_lowerVectorZorn x y

@[simp] theorem lower_upper_mul_diag (x y : Vec3) :
    zornMul (lowerVectorZorn y) (upperVectorZorn x) =
      zornMk 0 (dot3 y x) 0 0 := by
  simpa using lowerVectorZorn_mul_upperVectorZorn x y

end InfoGeometry.Algebra.Zorn
