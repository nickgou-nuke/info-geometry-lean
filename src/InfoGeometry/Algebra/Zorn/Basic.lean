import Mathlib.Data.Fin.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/--
A minimal dot/cross interface on `R^3`.
-/
structure CrossProduct3 (R : Type*) [CommRing R] where
  dot : (Fin 3 → R) → (Fin 3 → R) → R
  cross : (Fin 3 → R) → (Fin 3 → R) → (Fin 3 → R)

  dot_zero_left :
    ∀ v : Fin 3 → R, dot 0 v = 0
  dot_zero_right :
    ∀ v : Fin 3 → R, dot v 0 = 0

  cross_zero_left :
    ∀ v : Fin 3 → R, cross 0 v = 0
  cross_zero_right :
    ∀ v : Fin 3 → R, cross v 0 = 0

namespace ZornMatrix

variable {R : Type*} [CommRing R]

/--
Zorn determinant / split norm.

For

  X = [ a  x ]
      [ y  b ]

the determinant is

  detZ X = a b - v · w.
-/
def detZ (cp : CrossProduct3 R) (X : ZornMatrix R) : R :=
  X.a * X.b - cp.dot X.x X.y

/-- Quadratic/projective nullness. -/
def IsNull (cp : CrossProduct3 R) (X : ZornMatrix R) : Prop :=
  detZ cp X = 0

end ZornMatrix

end InfoGeometry.Algebra.Zorn
