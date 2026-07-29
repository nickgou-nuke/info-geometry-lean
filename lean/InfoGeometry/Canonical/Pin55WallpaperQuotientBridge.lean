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

/--
Finite bridge packet for the `Pin(5,5)` reflection quotient and the wallpaper
shadow.

The packet composes the checked finite owner lemmas:
* `Pin55.pin_quotient_to_weyl`,
* `Pin55WeylWallpaper.weyl_wallpaper_quotient_packet`,
* `WallpaperGroupPG.kleinBottlePresentation_relation`,
* `WallpaperKleinBottleCartan.wallpaperD4_is_klein_compatible`.
-/
def Pin55D5WallpaperQuotientPacket (v : Torus5D) (p : Lattice2D) : Prop :=
  (pin_reflection (alpha_12, fun _ => 0) (v, fun _ => 0)).1 =
      weyl_reflect v alpha_12 ∧
    project_2d (weyl_reflect v alpha_12) = (v 1, v 0) ∧
    project_2d (affine_shift (weyl_reflect v alpha_12)) =
      (v 1 + 1, v 0 + 1) ∧
    (WallpaperGroupPG.kleinBottlePresentation concretePG).glide
        ((WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation
          ((WallpaperGroupPG.kleinBottlePresentation concretePG).glide.symm p)) =
      (WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation.symm p ∧
    (∀ i : Fin 8, IsKleinCompatibleWallpaper (wallpaperD4 i))

namespace Pin55D5WallpaperQuotientPacket

variable {v : Torus5D} {p : Lattice2D}

theorem pin_to_weyl
    (h : Pin55D5WallpaperQuotientPacket v p) :
    (pin_reflection (alpha_12, fun _ => 0) (v, fun _ => 0)).1 =
      weyl_reflect v alpha_12 :=
  h.1

theorem wallpaper_mirror
    (h : Pin55D5WallpaperQuotientPacket v p) :
    project_2d (weyl_reflect v alpha_12) = (v 1, v 0) :=
  h.2.1

theorem wallpaper_glide
    (h : Pin55D5WallpaperQuotientPacket v p) :
    project_2d (affine_shift (weyl_reflect v alpha_12)) =
      (v 1 + 1, v 0 + 1) :=
  h.2.2.1

theorem klein_bottle_presentation
    (h : Pin55D5WallpaperQuotientPacket v p) :
    (WallpaperGroupPG.kleinBottlePresentation concretePG).glide
        ((WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation
          ((WallpaperGroupPG.kleinBottlePresentation concretePG).glide.symm p)) =
      (WallpaperGroupPG.kleinBottlePresentation concretePG).yTranslation.symm p :=
  h.2.2.2.1

theorem wallpaperD4_compatible
    (h : Pin55D5WallpaperQuotientPacket v p) :
    ∀ i : Fin 8, IsKleinCompatibleWallpaper (wallpaperD4 i) :=
  h.2.2.2.2

end Pin55D5WallpaperQuotientPacket

/-- Build the finite quotient packet from the checked owner lemmas. -/
theorem pin55_d5_wallpaper_quotient_packet
    (v : Torus5D) (p : Lattice2D) :
    Pin55D5WallpaperQuotientPacket v p := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using Pin55.pin_quotient_to_weyl v
  · exact weyl_projects_to_wallpaper_mirror v
  · exact affine_weyl_projects_to_glide_reflection v
  · exact concrete_kleinBottlePresentation_relation p
  · exact wallpaperD4_is_klein_compatible

end InfoGeometry.Canonical.Pin55WallpaperQuotientBridge
