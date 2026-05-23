import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Zorn composition norm

This file records the reduced Zorn norm multiplicativity on the explicit
coordinate carrier as a direct theorem.

It is the local H¹ rigidity layer for the split-octonion shadow.
This is a Zorn composition theorem, not a projection/Binet-Cauchy claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornComposition

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-- Zorn determinant readout on the explicit carrier. -/
abbrev detZ : ZornCoord → ℝ := zornNorm

/-- Zorn multiplication readout on the explicit carrier. -/
abbrev mulZ : ZornCoord → ZornCoord → ZornCoord := zornMul

/-- The Zorn determinant is multiplicative on the explicit carrier. -/
theorem detZ_mul (X Y : ZornCoord) :
    detZ (mulZ X Y) = detZ X * detZ Y := by
  simpa [detZ, mulZ] using zornNorm_mul X Y

/-- Left multiplication by a norm-one Zorn element preserves the determinant. -/
theorem detZ_left_mul_normOne
    (U X : ZornCoord)
    (hU : detZ U = 1) :
    detZ (mulZ U X) = detZ X := by
  rw [detZ_mul, hU, one_mul]

/-- Right multiplication by a norm-one Zorn element preserves the determinant. -/
theorem detZ_right_mul_normOne
    (X U : ZornCoord)
    (hU : detZ U = 1) :
    detZ (mulZ X U) = detZ X := by
  rw [detZ_mul, hU, mul_one]

end InfoGeometry.Canonical.ZornComposition
