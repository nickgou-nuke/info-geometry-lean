/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

variable {R : Type*} [Ring R]

/--
A composition datum for the Zorn split-octonion cell.

It extends the dot/cross interface with an abstract multiplication `mulZ`
and requires it to be strictly multiplicative on the Zorn determinant.
This is the honest composition theorem, avoiding partial/placeholder proofs.
-/
structure ZornCompositionDatum (R : Type*) [Ring R]
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

end InfoGeometry.Algebra.Zorn
