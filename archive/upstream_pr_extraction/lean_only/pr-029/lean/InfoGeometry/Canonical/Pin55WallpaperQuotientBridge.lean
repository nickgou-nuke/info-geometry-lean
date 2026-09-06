import InfoGeometry.Canonical.Pin55
import InfoGeometry.Canonical.Pin55WeylWallpaper
import InfoGeometry.Canonical.WallpaperKleinBottleCartan
import InfoGeometry.Topology.WallpaperKleinBottlePresentation

/-!
# Finite `Pin(5,5)` to wallpaper quotient bridge

This file packages the finite theorem chain that is actually available in the
repository:

* a split-signature `Pin(5,5)` reflection maps to the `D₅` Weyl reflection;
* that Weyl reflection projects to the wallpaper mirror and affine glide;
* the concrete `pg` wallpaper action satisfies the Klein-bottle relation;
* the eight displayed wallpaper point symmetries are Klein-compatible.

This is a finite quotient bridge, not a full classification theorem for
`O(5,5)`, `Pin(5,5)`, or the wallpaper groups.
-/

noncomputable section

namespace InfoGeometry.Canonical.Pin55WallpaperQuotientBridge

open InfoGeometry.Canonical.Pin55
open InfoGeometry.Canonical.Pin55WeylWallpaper
open InfoGeometry.Canonical.WallpaperKleinBottleCartan
open InfoGeometry.Topology.Wallpaper
open InfoGeometry.Topology.WallpaperKleinBottlePresentation

namespace Pin55D5WallpaperQuotientPacket

theorem pin_to_weyl (v : Torus5D) :
    (pin_reflection (alpha_12, fun _ => 0) (v, fun _ => 0)).1 =
      weyl_reflect v alpha_12 := by
  simpa using Pin55.pin_quotient_to_weyl v

theorem wallpaper_mirror (v : Torus5D) :
    project_2d (weyl_reflect v alpha_12) = (v 1, v 0) :=
  weyl_projects_to_wallpaper_mirror v

theorem wallpaper_glide (v : Torus5D) :
    project_2d (affine_shift (weyl_reflect v alpha_12)) =
      (v 1 + 1, v 0 + 1) :=
  affine_weyl_projects_to_glide_reflection v

theorem klein_bottle_presentation (p : Lattice2D) :
    (WallpaperGroupPG.kleinBottlePresentation concretePG).glide
        ((WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation
          ((WallpaperGroupPG.kleinBottlePresentation concretePG).glide.symm p)) =
      (WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation.symm p :=
  concrete_kleinBottlePresentation_relation p

theorem wallpaperD4_compatible :
    ∀ i : Fin 8, IsKleinCompatibleWallpaper (wallpaperD4 i) :=
  wallpaperD4_is_klein_compatible

end Pin55D5WallpaperQuotientPacket

/-- Build the finite quotient packet from the checked owner lemmas. -/
theorem pin55_d5_wallpaper_quotient_packet
    (v : Torus5D) (p : Lattice2D) :
    (pin_reflection (alpha_12, fun _ => 0) (v, fun _ => 0)).1 =
        weyl_reflect v alpha_12 ∧
      project_2d (weyl_reflect v alpha_12) = (v 1, v 0) ∧
      project_2d (affine_shift (weyl_reflect v alpha_12)) =
        (v 1 + 1, v 0 + 1) ∧
      (WallpaperGroupPG.kleinBottlePresentation concretePG).glide
          ((WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation
            ((WallpaperGroupPG.kleinBottlePresentation concretePG).glide.symm p)) =
        (WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation.symm p ∧
      (∀ i : Fin 8, IsKleinCompatibleWallpaper (wallpaperD4 i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using Pin55.pin_quotient_to_weyl v
  · exact weyl_projects_to_wallpaper_mirror v
  · exact affine_weyl_projects_to_glide_reflection v
  · exact concrete_kleinBottlePresentation_relation p
  · exact wallpaperD4_is_klein_compatible

end InfoGeometry.Canonical.Pin55WallpaperQuotientBridge
