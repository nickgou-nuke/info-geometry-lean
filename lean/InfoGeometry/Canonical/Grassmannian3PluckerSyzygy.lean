import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic

/-!
# A Grassmann–Plücker Relation for 3-by-n Matrices

This module defines the 3-by-3 minors of a matrix with three rows and proves
one standard four-term Grassmann–Plücker relation among them. The theorem is a
polynomial identity over a commutative ring. This file does not formalize an
associahedron or scattering amplitudes, nor does it claim to give a complete
presentation of the Plücker ideal.

1. **Plücker 3-Minors (`pluckerMinor3`)**:
   Explicit expansion of the 3x3 determinants of a 3xN matrix.

2. **A Grassmann–Plücker Relation**:
   For fixed indices `a, b` and `c, d, e, f`, the quadratic identity:
   `Δ(a,b,c)Δ(d,e,f) - Δ(a,b,d)Δ(c,e,f) + Δ(a,b,e)Δ(c,d,f) - Δ(a,b,f)Δ(c,d,e) = 0`.
-/

namespace InfoGeometry.Canonical.Grassmannian

variable {R : Type*} [CommRing R] {n : ℕ}

/-- 
Computes the 3x3 determinant minor Δ_{ijk} of a 3xn matrix.
Defined via cofactor expansion along the first row. 
-/
def pluckerMinor3 (C : Matrix (Fin 3) (Fin n) R) (i j k : Fin n) : R :=
  C 0 i * (C 1 j * C 2 k - C 1 k * C 2 j) -
  C 0 j * (C 1 i * C 2 k - C 1 k * C 2 i) +
  C 0 k * (C 1 i * C 2 j - C 1 j * C 2 i)

/-- Swapping the first two indices negates the minor. -/
theorem pluckerMinor3_antisymm12 (C : Matrix (Fin 3) (Fin n) R) (i j k : Fin n) :
    pluckerMinor3 C j i k = - pluckerMinor3 C i j k := by
  unfold pluckerMinor3; ring

/-- Swapping the last two indices negates the minor. -/
theorem pluckerMinor3_antisymm23 (C : Matrix (Fin 3) (Fin n) R) (i j k : Fin n) :
    pluckerMinor3 C i k j = - pluckerMinor3 C i j k := by
  unfold pluckerMinor3; ring

/-- The minor vanishes when its first two indices agree. -/
theorem pluckerMinor3_self12 (C : Matrix (Fin 3) (Fin n) R) (i k : Fin n) :
    pluckerMinor3 C i i k = 0 := by
  unfold pluckerMinor3; ring

/--
For any matrix with three rows, its 3-by-3 minors satisfy this four-term
Grassmann–Plücker relation. This is one relation in the Plücker family.
-/
theorem plucker3_syzygy (C : Matrix (Fin 3) (Fin n) R) (a b c d e f : Fin n) :
    pluckerMinor3 C a b c * pluckerMinor3 C d e f -
    pluckerMinor3 C a b d * pluckerMinor3 C c e f +
    pluckerMinor3 C a b e * pluckerMinor3 C c d f -
    pluckerMinor3 C a b f * pluckerMinor3 C c d e = 0 := by
  unfold pluckerMinor3
  ring

end InfoGeometry.Canonical.Grassmannian
