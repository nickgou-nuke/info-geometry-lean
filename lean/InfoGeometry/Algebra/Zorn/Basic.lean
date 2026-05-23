import InfoGeometry.Canonical.ZornSpinor

/-!
# InfoGeometry.Algebra.Zorn.Basic

This is the narrow algebra bridge for the repository's Zorn carrier.

It reuses the explicit canonical split-octonion carrier from
`InfoGeometry.Canonical.ZornSpinor` and exposes the local norm/determinant
readout under the algebra namespace.

No composition theorem is claimed here.
-/

namespace InfoGeometry.Algebra.Zorn

abbrev ZornMatrix (R : Type*) [CommRing R] := InfoGeometry.Canonical.ZornMatrix R

/-- The reduced Zorn determinant/norm `ab - x · y`. -/
def detZ {R : Type*} [CommRing R] (z : ZornMatrix R) : R :=
  z.a * z.b - InfoGeometry.Canonical.ZornMatrix.dot z.x z.y

/-- The Zorn multiplication inherited from the canonical carrier. -/
def mulZ {R : Type*} [CommRing R] (x y : ZornMatrix R) : ZornMatrix R :=
  x * y

@[simp] theorem detZ_def {R : Type*} [CommRing R] (z : ZornMatrix R) :
    detZ z = z.a * z.b - InfoGeometry.Canonical.ZornMatrix.dot z.x z.y :=
  rfl

@[simp] theorem mulZ_def {R : Type*} [CommRing R] (x y : ZornMatrix R) :
    mulZ x y = x * y :=
  rfl

end InfoGeometry.Algebra.Zorn
