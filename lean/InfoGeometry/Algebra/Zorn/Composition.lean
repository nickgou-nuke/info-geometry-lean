import InfoGeometry.Algebra.Zorn.Basic

/-!
# InfoGeometry.Algebra.Zorn.Composition

This file packages the split-octonion/Zorn determinant multiplicativity as a
composition datum.

The repository already owns the explicit Zorn carrier and the local null-cone
readouts.  This module does not invent a new multiplication table; it isolates
the exact `detZ` multiplicativity statement needed for the local H¹ rigidity
layer.

The composition law is recorded as data so that a later proof-complete instance
can be attached without changing the interface.
-/

namespace InfoGeometry.Algebra.Zorn

/--
Zorn composition datum.

This is the theorem-facing interface for the local split-octonion composition
law:

`detZ (mulZ X Y) = detZ X * detZ Y`.
-/
structure ZornCompositionDatum (R : Type*) [CommRing R] where
  detZ_mul :
    ∀ X Y : ZornMatrix R,
      detZ (mulZ X Y) = detZ X * detZ Y

namespace ZornCompositionDatum

variable {R : Type*} [CommRing R]

/-- Left multiplication by a norm-one Zorn element preserves `detZ`. -/
theorem detZ_left_mul_normOne
    (cp : ZornCompositionDatum R)
    (U X : ZornMatrix R)
    (hU : detZ U = 1) :
    detZ (mulZ U X) = detZ X := by
  rw [cp.detZ_mul, hU, one_mul]

/-- Right multiplication by a norm-one Zorn element preserves `detZ`. -/
theorem detZ_right_mul_normOne
    (cp : ZornCompositionDatum R)
    (X U : ZornMatrix R)
    (hU : detZ U = 1) :
    detZ (mulZ X U) = detZ X := by
  rw [cp.detZ_mul, hU, mul_one]

end ZornCompositionDatum

end InfoGeometry.Algebra.Zorn
