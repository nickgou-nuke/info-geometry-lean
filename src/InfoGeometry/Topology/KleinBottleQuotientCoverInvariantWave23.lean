/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinBottleOrbitQuotient

/-!
# Universal-cover invariance of the Klein orbit quotient

The quotient carrier is defined from the Brillouin torus.  The lifted glide
on the universal cover descends to the torus glide, and the orbit quotient
therefore identifies the two lifted points.  This file records that exact
compatibility at the cover-to-quotient level, without introducing a new
quotient carrier or asserting a surface classification.
-/

noncomputable section

namespace KleinBottleOrbitQuotient

open KleinBrillouinBase

/-- The orbit quotient is invariant under the lifted affine glide. -/
theorem quotientMap_coverToTorus_glide (k : Cover) :
    quotientMap (coverToTorus (glide k)) = quotientMap (coverToTorus k) := by
  rw [coverToTorus_glide, quotientMap_glide]

/-- The orbit quotient is invariant under the lifted longitudinal period. -/
theorem quotientMap_coverToTorus_tx (k : Cover) :
    quotientMap (coverToTorus (tx k)) = quotientMap (coverToTorus k) := by
  rw [coverToTorus_tx]

/-- The orbit quotient is invariant under the lifted transverse period. -/
theorem quotientMap_coverToTorus_ty (k : Cover) :
    quotientMap (coverToTorus (ty k)) = quotientMap (coverToTorus k) := by
  rw [coverToTorus_ty]

end KleinBottleOrbitQuotient
end noncomputable section
