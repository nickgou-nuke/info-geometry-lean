import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Canonical.SplitOctonionClassificationCore

/-!
# InfoGeometry.Algebra.Zorn.Associator

This file exposes the split-octonion associator defect in the algebra
namespace and re-exports the canonical nonzero associator witness.

It is the H^3 defect layer of the Zorn split-octonion shadow.
-/

namespace InfoGeometry.Algebra.Zorn

open InfoGeometry.Canonical.SplitOctonionClassificationCore.ZornMatrix

/-- The Zorn associator defect `(x * y) * z - x * (y * z)`. -/
def associatorDefect {R : Type*} [CommRing R]
    (x y z : ZornMatrix R) : ZornMatrix R :=
  (x * y) * z - x * (y * z)

@[simp] theorem associatorDefect_apply {R : Type*} [CommRing R]
    (x y z : ZornMatrix R) :
    associatorDefect x y z = (x * y) * z - x * (y * z) := by
  rfl

/--
A non-scalar Zorn element has a nonzero associator witness.

This is the local H^3 defect statement, imported from the canonical split
octonion classification layer.
-/
theorem exists_nonzero_associator_of_not_scalar
    {R : Type*} [CommRing R]
    {x : ZornMatrix R}
    (hx : ¬ ∃ r : R, x = r • (1 : ZornMatrix R)) :
    ∃ y z : ZornMatrix R, associatorDefect x y z ≠ 0 := by
  simpa [associatorDefect] using
    (nonzero_associator_of_not_scalar (R := R) (x := x) hx)

end InfoGeometry.Algebra.Zorn
