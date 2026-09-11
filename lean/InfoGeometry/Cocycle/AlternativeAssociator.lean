import Mathlib.Algebra.Ring.Associator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornSpinor

/-!
# InfoGeometry.Cocycle.AlternativeAssociator

Associator/coherence layer for the nonassociative branch of the cocycle
calculus.

This file owns the generic associator defect and its 4-term cocycle identity.
It does not claim that the split-octonion shadow proves a current algebra or a
WZW theorem. The point is only to make the bracketing defect explicit and
kernel-checked.
-/

noncomputable section

namespace InfoGeometry.Cocycle

section GenericAssociator

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- The associator defect `(x * y) * z - x * (y * z)`. -/
def associatorDefect (x y z : R) : R :=
  associator x y z

@[simp]
theorem associatorDefect_apply (x y z : R) :
    associatorDefect (R := R) x y z = (x * y) * z - x * (y * z) := by
  simpa [associatorDefect] using associator_apply (R := R) x y z

/--
The associator cocycle identity.

This is the algebraic coherence relation behind the `H^3`-type associator
layer.
-/
theorem associatorDefect_cocycle (a b c d : R) :
    a * associatorDefect (R := R) b c d
      - associatorDefect (R := R) (a * b) c d
      + associatorDefect (R := R) a (b * c) d
      - associatorDefect (R := R) a b (c * d)
      + associatorDefect (R := R) a b c * d = 0 := by
  simpa [associatorDefect] using
    (associator_cocycle (R := R) a b c d)

/-- The associator defect vanishes exactly when multiplication is associative. -/
theorem associatorDefect_eq_zero_iff_associative :
    associatorDefect (R := R) = 0 ↔ Std.Associative (fun x y : R => x * y) := by
  simpa [associatorDefect] using
    (associator_eq_zero_iff_associative (R := R))

end GenericAssociator

end InfoGeometry.Cocycle

namespace InfoGeometry.Canonical

section ZornAssociatorShadow

variable {R : Type*} [CommRing R]

/--
Split-octonion shadow associator defect on Zorn matrices.

This is only the bracketing defect of the supported Zorn model; it is not a
claim of an octonion closure theorem.
-/
def ZornMatrix.associatorDefect (x y z : ZornMatrix R) : ZornMatrix R :=
  (x * y) * z - x * (y * z)

@[simp]
theorem ZornMatrix.associatorDefect_apply (x y z : ZornMatrix R) :
    ZornMatrix.associatorDefect (R := R) x y z = (x * y) * z - x * (y * z) :=
  rfl

end ZornAssociatorShadow

end InfoGeometry.Canonical
