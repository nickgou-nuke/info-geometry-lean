import InfoGeometry.Algebra.Zorn.Basic

/-!
# InfoGeometry.Algebra.Zorn.Composition

Honest split-octonion composition surface.

This file provides the unconditional Zorn multiplication and the explicit H¹
rigidity identity (the Zorn determinant is multiplicative).
It separates quadratic null-preservation from projective automorphism status.

Repository policy boundary:
this is not ordinary associative matrix determinant multiplicativity
(and not a Binet-Cauchy theorem surface). It is the split-octonion/Zorn
composition identity for a custom nonassociative product.
-/

namespace InfoGeometry.Algebra.Zorn

variable {R : Type*} [CommRing R]

namespace ZornMatrix

/--
Zorn matrix multiplication over a commutative ring.
This defines the multiplication for the split-octonion algebra.
-/
def mulZ (X Y : ZornMatrix R) : ZornMatrix R :=
  { a := X.a * Y.a + InfoGeometry.Canonical.ZornMatrix.dot X.x Y.y
    b := X.b * Y.b + InfoGeometry.Canonical.ZornMatrix.dot X.y Y.x
    x := X.a • Y.x + Y.b • X.x - InfoGeometry.Canonical.ZornMatrix.cross X.y Y.y
    y := X.b • Y.y + Y.a • X.y + InfoGeometry.Canonical.ZornMatrix.cross X.x Y.x }

omit [CommRing R] in
lemma expand_fin3 (v : Fin 3 → R) : v = ![v 0, v 1, v 2] := by
  ext i
  fin_cases i <;> rfl

/-- The Zorn determinant is multiplicative over Zorn matrix multiplication. -/
theorem detZ_mul (X Y : ZornMatrix R) : detZ (mulZ X Y) = detZ X * detZ Y := by
  dsimp [detZ, mulZ]
  rw [expand_fin3 X.x, expand_fin3 X.y, expand_fin3 Y.x, expand_fin3 Y.y]
  simp [InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  ring

/-- Left Zorn multiplication preserves the null cone. -/
theorem left_mul_preserves_null
    (U X : ZornMatrix R)
    (hX : IsNull X) :
    IsNull (mulZ U X) := by
  unfold IsNull at *
  rw [detZ_mul U X, hX, mul_zero]

/-- Right Zorn multiplication preserves the null cone. -/
theorem right_mul_preserves_null
    (X U : ZornMatrix R)
    (hX : IsNull X) :
    IsNull (mulZ X U) := by
  unfold IsNull at *
  rw [detZ_mul X U, hX, zero_mul]

end ZornMatrix

end InfoGeometry.Algebra.Zorn


