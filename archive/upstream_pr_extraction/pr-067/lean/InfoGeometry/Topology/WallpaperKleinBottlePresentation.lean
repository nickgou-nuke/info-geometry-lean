import InfoGeometry.Topology.WallpaperSymmetry

/-!
# Wallpaper `pg` Klein-bottle presentation property

This module packages the finite `pg` wallpaper relation into a theorem-safe
presentation property for the Klein-bottle relation.

It does **not** prove that a topological quotient has been constructed, that the
quotient is a manifold, or that the quotient is homeomorphic to the Klein
bottle. It only records the exact pointwise group-action relation
`G ∘ T_y ∘ G⁻¹ = T_y⁻¹` on the lattice chart.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `WallpaperGroupPG.kleinBottlePresentation`
* `WallpaperGroupPG.kleinBottlePresentation_relation`
* `concrete_kleinBottlePresentation_relation`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

None in this file.

#### BUCKET 3: OPEN CLOSURE DEBT

* no quotient carrier;
* no quotient-space topology;
* no proof that the resulting quotient is homeomorphic to `K^2`;
* no Brillouin-zone or semimetal invariant classification.
-/

noncomputable section

namespace InfoGeometry.Topology.WallpaperKleinBottlePresentation

open InfoGeometry.Topology.Wallpaper

namespace WallpaperGroupPG

theorem kleinBottlePresentation_relation (pg : WallpaperGroupPG) (p : Lattice2D) :
    pg.G (pg.T_y (pg.G.symm p)) = pg.T_y.symm p := by
  have h := pg.h_commutation (pg.G.symm p)
  simpa using h

end WallpaperGroupPG

/-- The concrete Euclidean `pg` action yields the finite Klein-bottle presentation relation. -/
theorem concrete_kleinBottlePresentation_relation (p : Lattice2D) :
    concretePG.G (concretePG.T_y (concretePG.G.symm p)) = concretePG.T_y.symm p :=
  WallpaperGroupPG.kleinBottlePresentation_relation concretePG p

end InfoGeometry.Topology.WallpaperKleinBottlePresentation

end noncomputable section
