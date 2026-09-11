import InfoGeometry.Algebra.CuntzN
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace CuntzAlgebra

variable {A : Type*} [Ring A] [StarRing A]

/-- The two-generator instance of the generic Cuntz owner. -/
abbrev Cuntz2Isometries (A : Type*) [Ring A] [StarRing A] :=
  InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) A

/-- The first generator, exposed only as a named index of the generic owner. -/
def S1 (c : Cuntz2Isometries A) : A := c.S 0

/-- The second generator, exposed only as a named index of the generic owner. -/
def S2 (c : Cuntz2Isometries A) : A := c.S 1

theorem h_isometry1 (c : Cuntz2Isometries A) :
    star (S1 c) * S1 c = 1 := by
  simpa [S1] using c.isometry 0 0

theorem h_isometry2 (c : Cuntz2Isometries A) :
    star (S2 c) * S2 c = 1 := by
  simpa [S2] using c.isometry 1 1

theorem h_range_sum (c : Cuntz2Isometries A) :
    S1 c * star (S1 c) + S2 c * star (S2 c) = 1 := by
  simpa [S1, S2] using c.range_sum

def rangeProj1 (c : Cuntz2Isometries A) : A :=
  S1 c * star (S1 c)

def rangeProj2 (c : Cuntz2Isometries A) : A :=
  S2 c * star (S2 c)

theorem rangeProj1_idem (c : Cuntz2Isometries A) :
    rangeProj1 c * rangeProj1 c = rangeProj1 c := by
  simpa [rangeProj1, S1] using
    InfoGeometry.Algebra.Cuntz.range_projection_idempotent c 0

theorem rangeProj2_idem (c : Cuntz2Isometries A) :
    rangeProj2 c * rangeProj2 c = rangeProj2 c := by
  simpa [rangeProj2, S2] using
    InfoGeometry.Algebra.Cuntz.range_projection_idempotent c 1

theorem isometries_ortho (c : Cuntz2Isometries A) :
    star (S1 c) * S2 c = 0 := by
  simpa [S1, S2] using c.isometry 0 1

theorem rangeProjs_ortho (c : Cuntz2Isometries A) :
    rangeProj1 c * rangeProj2 c = 0 := by
  simpa [rangeProj1, rangeProj2, S1, S2] using
    InfoGeometry.Algebra.Cuntz.range_projection_orthogonal c 0 1 (by decide)

end CuntzAlgebra
