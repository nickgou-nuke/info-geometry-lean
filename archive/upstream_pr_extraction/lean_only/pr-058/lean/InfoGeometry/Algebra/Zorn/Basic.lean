import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.ZornSpinor

/-!
# InfoGeometry.Algebra.Zorn.Basic

Basic Zorn vector-matrix data for the local split-octonion cell.
This module now uses the canonical `ZornMatrix` carrier.

Repository policy boundary:
Zorn cells are not ordinary associative `2×2` matrix multiplication objects.
They are vector-matrix coordinates for split-octonion algebraic data with a
custom nonassociative product supplied in dedicated owner modules.
The determinant lane is the split-octonion composition identity (`detZ_mul`),
not ordinary matrix determinant multiplicativity.
-/

namespace InfoGeometry.Algebra.Zorn

/-- Use the canonical Zorn matrix carrier. -/
abbrev ZornMatrix (R : Type*) [CommRing R] := InfoGeometry.Canonical.ZornMatrix R

namespace ZornMatrix

variable {R : Type*} [CommRing R]

/--
Zorn determinant / split norm.

For

  X = [ a  x ]
      [ y  b ]

the determinant is

  detZ X = a b - x · y.
-/
def detZ (X : ZornMatrix R) : R :=
  X.a * X.b - InfoGeometry.Canonical.ZornMatrix.dot X.x X.y

/-- Quadratic/projective nullness. -/
def IsNull (X : ZornMatrix R) : Prop :=
  detZ X = 0

end ZornMatrix

end InfoGeometry.Algebra.Zorn

