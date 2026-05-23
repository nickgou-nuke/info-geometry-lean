import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Zorn composition norm

This file packages the split-octonion composition law for the explicit Zorn
carrier as proof-carrying data.

It does not prove the determinant multiplicativity theorem from scratch. The
theorem surface is the local H¹ composition law

  `zornNorm (zornMul X Y) = zornNorm X * zornNorm Y`

and the norm-one rigidity corollaries below.
-/

namespace InfoGeometry.Canonical.ZornComposition

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-- Zorn determinant readout on the explicit carrier. -/
abbrev detZ : ZornCoord → ℝ := zornNorm

/-- Zorn multiplication readout on the explicit carrier. -/
abbrev mulZ : ZornCoord → ZornCoord → ZornCoord := zornMul

/--
Proof-carrying data for the Zorn composition law.

This is the no-cheat interface for the multiplicative split-octonion norm.
-/
structure ZornCompositionDatum where
  detZ_mul :
    ∀ X Y : ZornCoord,
      detZ (mulZ X Y) = detZ X * detZ Y

namespace ZornCompositionDatum

/-- Left multiplication by a norm-one Zorn element preserves the Zorn determinant. -/
theorem detZ_left_mul_normOne
    (cp : ZornCompositionDatum)
    (U X : ZornCoord)
    (hU : detZ U = 1) :
    detZ (mulZ U X) = detZ X := by
  rw [cp.detZ_mul U X, hU, one_mul]

/-- Right multiplication by a norm-one Zorn element preserves the Zorn determinant. -/
theorem detZ_right_mul_normOne
    (cp : ZornCompositionDatum)
    (X U : ZornCoord)
    (hU : detZ U = 1) :
    detZ (mulZ X U) = detZ X := by
  rw [cp.detZ_mul X U, hU, mul_one]

end ZornCompositionDatum

end InfoGeometry.Canonical.ZornComposition
