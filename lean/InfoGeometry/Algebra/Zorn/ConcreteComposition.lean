import InfoGeometry.Algebra.Zorn.Composition
import InfoGeometry.Canonical.ZornComposition
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.Zorn.ConcreteComposition

Concrete split-octonion composition bridge on the algebraic Zorn carrier.

This file instantiates the abstract `ZornCompositionDatum` on the concrete
real `Fin 3` model, using the explicit reduced norm multiplicativity theorem
already proved in the canonical carrier.
-/

namespace InfoGeometry.Algebra.Zorn

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

abbrev Vec3 : Type := Fin 3 → ℝ

/-- The concrete dot product on `Vec3`. -/
def dot3 (u v : Vec3) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The concrete cross product on `Vec3`. -/
def cross3 (u v : Vec3) : Vec3 :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

theorem dot3_zero_left (v : Vec3) : dot3 0 v = 0 := by
  simp [dot3]

theorem dot3_zero_right (v : Vec3) : dot3 v 0 = 0 := by
  simp [dot3]

theorem cross3_zero_left (v : Vec3) : cross3 0 v = 0 := by
  ext i <;> fin_cases i <;> simp [cross3]

theorem cross3_zero_right (v : Vec3) : cross3 v 0 = 0 := by
  ext i <;> fin_cases i <;> simp [cross3]

/-- The concrete `CrossProduct3` structure for the real split-octonion cell. -/
def concreteCrossProduct3 : CrossProduct3 ℝ where
  dot := dot3
  cross := cross3
  dot_zero_left := dot3_zero_left
  dot_zero_right := dot3_zero_right
  cross_zero_left := cross3_zero_left
  cross_zero_right := cross3_zero_right

/-- The concrete Zorn multiplication on `ZornMatrix ℝ Vec3`. -/
def mulZ (X Y : ZornMatrix ℝ) : ZornMatrix ℝ where
  a := X.a * Y.a + dot3 X.x Y.y
  b := X.b * Y.b + dot3 X.y Y.x
  x := X.a • Y.x + Y.b • X.x - cross3 X.y Y.y
  y := X.b • Y.y + Y.a • X.y + cross3 X.x Y.x

/-- Coordinate transport into the explicit canonical carrier. -/
def toCoord (X : ZornMatrix ℝ) : ZornCoord :=
  (X.a, X.b, X.x, X.y)

/-- The determinant on the concrete carrier agrees with the canonical norm. -/
theorem detZ_eq_zornNorm (X : ZornMatrix ℝ) :
    ZornMatrix.detZ concreteCrossProduct3 X =
      zornNorm (toCoord X) := by
  rfl

/-- Multiplication is the explicit split-octonion multiplication. -/
theorem mulZ_eq_zornMul (X Y : ZornMatrix ℝ) :
    toCoord (mulZ X Y) = zornMul (toCoord X) (toCoord Y) := by
  ext <;> rfl

/-- The concrete Zorn determinant is multiplicative. -/
theorem detZ_mul (X Y : ZornMatrix ℝ) :
    ZornMatrix.detZ concreteCrossProduct3 (mulZ X Y)
      =
    ZornMatrix.detZ concreteCrossProduct3 X *
      ZornMatrix.detZ concreteCrossProduct3 Y := by
  change zornNorm (toCoord (mulZ X Y)) = zornNorm (toCoord X) * zornNorm (toCoord Y)
  rw [mulZ_eq_zornMul]
  simpa using zornNorm_mul (toCoord X) (toCoord Y)

/-- Concrete Zorn composition datum on the real split-octonion carrier. -/
def concreteCompositionDatum : ZornCompositionDatum ℝ where
  dot := dot3
  cross := cross3
  dot_zero_left := dot3_zero_left
  dot_zero_right := dot3_zero_right
  cross_zero_left := cross3_zero_left
  cross_zero_right := cross3_zero_right
  mulZ := mulZ
  detZ_mul := detZ_mul

namespace concreteCompositionDatum

/-- Left multiplication by a norm-one concrete Zorn element preserves the determinant. -/
theorem detZ_left_mul_normOne
    (U X : ZornMatrix ℝ)
    (hU : ZornMatrix.detZ concreteCrossProduct3 U = 1) :
    ZornMatrix.detZ concreteCrossProduct3 (mulZ U X) =
      ZornMatrix.detZ concreteCrossProduct3 X := by
  rw [detZ_mul, hU, one_mul]

/-- Right multiplication by a norm-one concrete Zorn element preserves the determinant. -/
theorem detZ_right_mul_normOne
    (X U : ZornMatrix ℝ)
    (hU : ZornMatrix.detZ concreteCrossProduct3 U = 1) :
    ZornMatrix.detZ concreteCrossProduct3 (mulZ X U) =
      ZornMatrix.detZ concreteCrossProduct3 X := by
  rw [detZ_mul, hU, mul_one]

end concreteCompositionDatum

end InfoGeometry.Algebra.Zorn
