import InfoGeometry.Canonical.Grassmannian3PluckerSyzygy
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Positivity of a Four-Term Relation for 3-by-n Matrices

Building on `plucker3_syzygy`, this module defines matrix representatives with
strictly positive ordered maximal minors and proves positivity of one side of
that relation. It does not define cluster mutations, an associahedron, or
amplituhedron boundary dynamics.

1. **Positive Grassmannian Gr_{>0}(3, n)**:
   A configuration is strictly positive if all ordered 3x3 Plücker minors
   are strictly positive.
2. **Positive side of one relation**:
   For six strictly ordered indices, one side is a sum of positive products.
-/

namespace InfoGeometry.Canonical.Grassmannian

variable {n : ℕ}

/--
An `n`-column matrix representative for a point of `Gr_{>0}(3,n)`: `n` must
be at least three and every ordered maximal minor must be strictly positive.
This predicate is on matrix representatives, not quotient points.
-/
def IsPositiveGrassmannian3 (C : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  3 ≤ n ∧ ∀ (i j k : Fin n), i < j → j < k → 0 < pluckerMinor3 C i j k

/--
For six strictly ordered indices, the corresponding side of the four-term
Plücker relation is positive when all ordered maximal minors are positive.
-/
theorem plucker3_syzygy_positivity
    (C : Matrix (Fin 3) (Fin n) ℝ)
    (hPos : IsPositiveGrassmannian3 C)
    (a b c d e f : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) (hef : e < f) :
    0 < pluckerMinor3 C a b d * pluckerMinor3 C c e f +
        pluckerMinor3 C a b f * pluckerMinor3 C c d e := by
  have hMinors := hPos.2
  have habc : 0 < pluckerMinor3 C a b c := hMinors a b c hab hbc
  have hdef : 0 < pluckerMinor3 C d e f := hMinors d e f hde hef

  have hbd : b < d := lt_trans hbc hcd
  have hce : c < e := lt_trans hcd hde
  have hbe : b < e := lt_trans hbd hde
  have hcf : c < f := lt_trans hce hef
  have hdf : d < f := lt_trans hde hef

  have habe : 0 < pluckerMinor3 C a b e := hMinors a b e hab hbe
  have hcdf : 0 < pluckerMinor3 C c d f := hMinors c d f hcd hdf

  have h1 : 0 < pluckerMinor3 C a b c * pluckerMinor3 C d e f := mul_pos habc hdef
  have h2 : 0 < pluckerMinor3 C a b e * pluckerMinor3 C c d f := mul_pos habe hcdf

  have h_sum_pos : 0 < pluckerMinor3 C a b c * pluckerMinor3 C d e f +
                       pluckerMinor3 C a b e * pluckerMinor3 C c d f := add_pos h1 h2

  have h_syz := plucker3_syzygy C a b c d e f

  have h_eq : pluckerMinor3 C a b d * pluckerMinor3 C c e f +
              pluckerMinor3 C a b f * pluckerMinor3 C c d e =
              pluckerMinor3 C a b c * pluckerMinor3 C d e f +
              pluckerMinor3 C a b e * pluckerMinor3 C c d f := by
    linarith [h_syz]

  rw [h_eq]
  exact h_sum_pos

end InfoGeometry.Canonical.Grassmannian
