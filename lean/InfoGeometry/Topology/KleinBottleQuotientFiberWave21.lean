/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinBottleOrbitQuotient

/-!
# Exact fibers of the Klein orbit quotient

The orbit quotient is already constructed from the free torus glide.  This
module records the resulting finite-fiber theorem: every quotient fiber is
exactly one glide orbit, and therefore has two points because the glide has no
fixed point.  No surface classification or manifold structure is inferred.
-/

noncomputable section

namespace KleinBottleOrbitQuotient

open KleinBrillouinBase

/-- The fiber over a torus point is exactly its two-point glide orbit. -/
theorem quotientMap_fiber_eq_glide_pair (k : BrillouinTorus) :
    quotientMap ⁻¹' ({quotientMap k} : Set KleinBrillouinQuotient) =
      ({k, torusGlide k} : Set BrillouinTorus) := by
  ext q
  constructor
  · intro hq
    have hEq : quotientMap q = quotientMap k := by
      exact hq
    have hrel : q = k ∨ q = torusGlide k :=
      (quotientMap_eq_iff k q).mp hEq.symm
    exact hrel
  · intro hq
    rcases hq with rfl | rfl
    · rfl
    · exact quotientMap_glide k

/-- Every fiber of the Klein orbit quotient has exactly two points. -/
theorem quotientMap_fiber_ncard (k : BrillouinTorus) :
    (quotientMap ⁻¹' ({quotientMap k} : Set KleinBrillouinQuotient)).ncard = 2 := by
  rw [quotientMap_fiber_eq_glide_pair]
  exact Set.ncard_pair (Ne.symm (torusGlide_ne_self k))

end KleinBottleOrbitQuotient
end noncomputable section
