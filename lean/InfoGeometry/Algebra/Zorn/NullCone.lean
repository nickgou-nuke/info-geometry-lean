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

/-- The positive diagonal projector. -/
def pPlus : ZornCoord :=
  zornMk 1 0 0 0

/-- The negative diagonal projector. -/
def pMinus : ZornCoord :=
  zornMk 0 1 0 0

@[simp] theorem vec3_zero : (![0, 0, 0] : Vec3) = 0 := by
  funext i; fin_cases i <;> simp

@[simp] theorem vec3_splat (x : Vec3) : ![x 0, x 1, x 2] = x := by
  funext i; fin_cases i <;> simp

@[simp] theorem pPlus_idempotent :
    zornMul pPlus pPlus = pPlus := by
  ext <;> simp [pPlus, zornMul, zornMk, dot3, cross3]

@[simp] theorem pMinus_idempotent :
    zornMul pMinus pMinus = pMinus := by
  ext <;> simp [pMinus, zornMul, zornMk, dot3, cross3]

@[simp] theorem pPlus_mul_pMinus :
    zornMul pPlus pMinus = 0 := by
  ext <;> simp [pPlus, pMinus, zornMul, zornMk, dot3, cross3]

@[simp] theorem pMinus_mul_pPlus :
    zornMul pMinus pPlus = 0 := by
  ext <;> simp [pPlus, pMinus, zornMul, zornMk, dot3, cross3]

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

theorem upperVector_left_supported_on_pPlus (x : Vec3) :
    zornMul pPlus (upperVectorZorn x) = upperVectorZorn x := by
  ext <;> simp [pPlus, upperVectorZorn, zornMul, zornMk, dot3, cross3]

theorem upperVector_right_supported_on_pMinus (x : Vec3) :
    zornMul (upperVectorZorn x) pMinus = upperVectorZorn x := by
  ext <;> simp [pMinus, upperVectorZorn, zornMul, zornMk, dot3, cross3]

theorem lowerVector_left_supported_on_pMinus (y : Vec3) :
    zornMul pMinus (lowerVectorZorn y) = lowerVectorZorn y := by
  ext <;> simp [pMinus, lowerVectorZorn, zornMul, zornMk, dot3, cross3]

theorem lowerVector_right_supported_on_pPlus (y : Vec3) :
    zornMul (lowerVectorZorn y) pPlus = lowerVectorZorn y := by
  ext <;> simp [pPlus, lowerVectorZorn, zornMul, zornMk, dot3, cross3]

/-- The positive diagonal projector lies on the Zorn null cone. -/
@[simp] theorem pPlus_isZornNull :
    IsZornNull pPlus := by
  simp [IsZornNull, pPlus, zornNorm, zornMk, dot3]

/-- The negative diagonal projector lies on the Zorn null cone. -/
@[simp] theorem pMinus_isZornNull :
    IsZornNull pMinus := by
  simp [IsZornNull, pMinus, zornNorm, zornMk, dot3]

/-- Every upper off-diagonal lightray representative is null. -/
@[simp] theorem upperVector_isZornNull (x : Vec3) :
    IsZornNull (upperVectorZorn x) := by
  simp [IsZornNull, upperVectorZorn, zornNorm, zornMk, dot3]

/-- Every lower off-diagonal lightray representative is null. -/
@[simp] theorem lowerVector_isZornNull (y : Vec3) :
    IsZornNull (lowerVectorZorn y) := by
  simp [IsZornNull, lowerVectorZorn, zornNorm, zornMk, dot3]

end InfoGeometry.Algebra.Zorn
