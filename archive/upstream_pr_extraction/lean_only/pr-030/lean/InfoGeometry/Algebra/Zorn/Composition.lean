import InfoGeometry.Algebra.Zorn.Basic

/-!
# InfoGeometry.Algebra.Zorn.Composition

Honest split-octonion composition surface.

This file provides the `ZornCompositionDatum` interface that wraps
the explicit H¹ rigidity identity (the Zorn determinant is multiplicative).
It separates quadratic null-preservation from projective automorphism status.

Repository policy boundary:
this is not ordinary associative matrix determinant multiplicativity
(and not a Binet-Cauchy theorem surface). It is the split-octonion/Zorn
composition identity for a custom nonassociative product.
-/

namespace InfoGeometry.Algebra.Zorn

variable {R : Type*} [CommRing R]

/--
A composition datum for the Zorn split-octonion cell.

It extends the dot/cross interface with an abstract multiplication `mulZ`
and requires it to be strictly multiplicative on the Zorn determinant.
This is the honest composition theorem, avoiding partial/placeholder proofs.
-/
structure ZornCompositionDatum (R : Type*) [CommRing R]
    extends CrossProduct3 R where
  mulZ : ZornMatrix R → ZornMatrix R → ZornMatrix R

  detZ_mul :
    ∀ X Y : ZornMatrix R,
      ZornMatrix.detZ toCrossProduct3 (mulZ X Y)
      =
      ZornMatrix.detZ toCrossProduct3 X *
      ZornMatrix.detZ toCrossProduct3 Y

namespace ZornCompositionDatum

variable (cp : ZornCompositionDatum R)

/-- Left Zorn multiplication preserves the null cone. -/
theorem left_mul_preserves_null
    (U X : ZornMatrix R)
    (hX : ZornMatrix.IsNull cp.toCrossProduct3 X) :
    ZornMatrix.IsNull cp.toCrossProduct3 (cp.mulZ U X) := by
  unfold ZornMatrix.IsNull at *
  rw [cp.detZ_mul U X, hX, mul_zero]

/-- Right Zorn multiplication preserves the null cone. -/
theorem right_mul_preserves_null
    (X U : ZornMatrix R)
    (hX : ZornMatrix.IsNull cp.toCrossProduct3 X) :
    ZornMatrix.IsNull cp.toCrossProduct3 (cp.mulZ X U) := by
  unfold ZornMatrix.IsNull at *
  rw [cp.detZ_mul X U, hX, zero_mul]

end ZornCompositionDatum

end InfoGeometry.Algebra.Zorn
