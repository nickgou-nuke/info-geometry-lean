import InfoGeometry.Canonical.ZornComposition

/-!
# InfoGeometry.Algebra.Zorn.Composition

This file exposes the explicit split-octonion composition law in the algebra
namespace.

The proof is the canonical H¹ rigidity identity on the concrete Zorn carrier.
It is a Zorn composition theorem, not a Binet-Cauchy or projection statement.
-/

namespace InfoGeometry.Algebra.Zorn

/-- The Zorn determinant is multiplicative. -/
theorem detZ_mul (X Y : InfoGeometry.Canonical.ZornVectorMatrixExplicit.ZornCoord) :
    InfoGeometry.Canonical.ZornComposition.detZ
      (InfoGeometry.Canonical.ZornComposition.mulZ X Y)
      =
    InfoGeometry.Canonical.ZornComposition.detZ X *
    InfoGeometry.Canonical.ZornComposition.detZ Y := by
  simpa using InfoGeometry.Canonical.ZornComposition.detZ_mul X Y

/-- Left multiplication by a norm-one Zorn element preserves the determinant. -/
theorem detZ_left_mul_normOne
    (U X : InfoGeometry.Canonical.ZornVectorMatrixExplicit.ZornCoord)
    (hU : InfoGeometry.Canonical.ZornComposition.detZ U = 1) :
    InfoGeometry.Canonical.ZornComposition.detZ
      (InfoGeometry.Canonical.ZornComposition.mulZ U X)
      =
    InfoGeometry.Canonical.ZornComposition.detZ X := by
  simpa using
    InfoGeometry.Canonical.ZornComposition.detZ_left_mul_normOne U X hU

/-- Right multiplication by a norm-one Zorn element preserves the determinant. -/
theorem detZ_right_mul_normOne
    (X U : InfoGeometry.Canonical.ZornVectorMatrixExplicit.ZornCoord)
    (hU : InfoGeometry.Canonical.ZornComposition.detZ U = 1) :
    InfoGeometry.Canonical.ZornComposition.detZ
      (InfoGeometry.Canonical.ZornComposition.mulZ X U)
      =
    InfoGeometry.Canonical.ZornComposition.detZ X := by
  simpa using
    InfoGeometry.Canonical.ZornComposition.detZ_right_mul_normOne X U hU

/-- Left Zorn multiplication preserves the null cone. -/
theorem left_mul_preserves_null
    (U X : InfoGeometry.Canonical.ZornVectorMatrixExplicit.ZornCoord)
    (hX : InfoGeometry.Canonical.ZornVectorMatrixExplicit.IsZornNull X) :
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.IsZornNull
      (InfoGeometry.Canonical.ZornComposition.mulZ U X) := by
  unfold InfoGeometry.Canonical.ZornVectorMatrixExplicit.IsZornNull at *
  change InfoGeometry.Canonical.ZornComposition.detZ (InfoGeometry.Canonical.ZornComposition.mulZ U X) = 0
  rw [InfoGeometry.Canonical.ZornComposition.detZ_mul, hX, mul_zero]

/-- Right Zorn multiplication preserves the null cone. -/
theorem right_mul_preserves_null
    (X U : InfoGeometry.Canonical.ZornVectorMatrixExplicit.ZornCoord)
    (hX : InfoGeometry.Canonical.ZornVectorMatrixExplicit.IsZornNull X) :
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.IsZornNull
      (InfoGeometry.Canonical.ZornComposition.mulZ X U) := by
  unfold InfoGeometry.Canonical.ZornVectorMatrixExplicit.IsZornNull at *
  change InfoGeometry.Canonical.ZornComposition.detZ (InfoGeometry.Canonical.ZornComposition.mulZ X U) = 0
  rw [InfoGeometry.Canonical.ZornComposition.detZ_mul, hX, zero_mul]

end InfoGeometry.Algebra.Zorn
