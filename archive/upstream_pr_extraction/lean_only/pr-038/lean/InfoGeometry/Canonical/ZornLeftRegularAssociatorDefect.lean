import Mathlib
import InfoGeometry.Canonical.ZornSpinor

/-!
# Native left-regular action and the Zorn associator defect

The canonical Zorn product is nonassociative.  This owner records the exact
function-level defect of the left-regular action.  A `Module.End` lift is
intentionally deferred until bilinearity certificates for the native product
are exposed by a separate owner.
-/

namespace InfoGeometry.Canonical

open ZornMatrix

variable {K : Type*} [CommRing K]

def leftRegular (X : ZornMatrix K) : ZornMatrix K → ZornMatrix K :=
  fun Y => X * Y

def associator (X Y Z : ZornMatrix K) : ZornMatrix K :=
  (X * Y) * Z - X * (Y * Z)

@[simp] theorem leftRegular_apply (X Y : ZornMatrix K) :
    leftRegular X Y = X * Y := rfl

theorem leftRegular_comp_sub_leftRegular_mul
    (X Y Z : ZornMatrix K) :
    leftRegular X (leftRegular Y Z) - leftRegular (X * Y) Z =
      -associator X Y Z := by
  change X * (Y * Z) - (X * Y) * Z =
    -((X * Y) * Z - X * (Y * Z))
  abel

theorem leftRegular_multiplicative_at
    (X Y Z : ZornMatrix K)
    (h : associator X Y Z = 0) :
    leftRegular X (leftRegular Y Z) = leftRegular (X * Y) Z := by
  have hd := leftRegular_comp_sub_leftRegular_mul X Y Z
  rw [h, neg_zero] at hd
  exact sub_eq_zero.mp hd

end InfoGeometry.Canonical
