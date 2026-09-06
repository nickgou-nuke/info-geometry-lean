import InfoGeometry.Topology.WallpaperSymmetry

/-!
# Wallpaper `pg` Klein-bottle presentation witness

This module packages the finite `pg` wallpaper relation into a theorem-safe
presentation witness for the Klein-bottle relation.

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

/--
Finite presentation witness for the pointwise Klein-bottle relation carried by a
`pg` wallpaper action.
-/
structure KleinBottlePresentationWitness where
  xTranslation : Lattice2D ≃ Lattice2D
  yTranslation : Lattice2D ≃ Lattice2D
  glide : Lattice2D ≃ Lattice2D
  glide_squared_eq_xTranslation : ∀ p : Lattice2D, glide (glide p) = xTranslation p
  glide_conjugates_yTranslation_to_inverse :
    ∀ p : Lattice2D, glide (yTranslation (glide.symm p)) = yTranslation.symm p

namespace WallpaperGroupPG

/-- Any `pg` wallpaper package determines a finite Klein-bottle presentation witness. -/
def kleinBottlePresentation (pg : WallpaperGroupPG) : KleinBottlePresentationWitness where
  xTranslation := pg.T_x
  yTranslation := pg.T_y
  glide := pg.G
  glide_squared_eq_xTranslation := pg.h_glide_squared
  glide_conjugates_yTranslation_to_inverse := by
    intro p
    have h := pg.h_commutation (pg.G.symm p)
    simpa using h

/-- Read back the pointwise Klein-bottle presentation relation from the witness. -/
theorem kleinBottlePresentation_relation (pg : WallpaperGroupPG) (p : Lattice2D) :
    (WallpaperGroupPG.kleinBottlePresentation pg).glide
        ((WallpaperGroupPG.kleinBottlePresentation pg).yTranslation
          ((WallpaperGroupPG.kleinBottlePresentation pg).glide.symm p)) =
      ((WallpaperGroupPG.kleinBottlePresentation pg).yTranslation.symm p) :=
  (WallpaperGroupPG.kleinBottlePresentation pg).glide_conjugates_yTranslation_to_inverse p

end WallpaperGroupPG

/-- The concrete Euclidean `pg` action yields the finite Klein-bottle presentation relation. -/
theorem concrete_kleinBottlePresentation_relation (p : Lattice2D) :
    (WallpaperGroupPG.kleinBottlePresentation concretePG).glide
        ((WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation
          ((WallpaperGroupPG.kleinBottlePresentation concretePG).glide.symm p)) =
      ((WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation.symm p) :=
  WallpaperGroupPG.kleinBottlePresentation_relation concretePG p

end InfoGeometry.Topology.WallpaperKleinBottlePresentation

end noncomputable section
