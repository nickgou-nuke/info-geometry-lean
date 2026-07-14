import Mathlib
import InfoGeometry.Canonical.KleinBottleWallpaper
import InfoGeometry.Canonical.WallpaperKleinBottleCartan
import InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
import InfoGeometry.Canonical.WallpaperPin55RootCrossSection

/-!
# Wallpaper / Pin(5,5) summary ledger

Theorem-honest finite summary table for the Klein-compatible wallpaper and
Pin(5,5)/O(5,5) cross-section lane.

Closed content assembled here:

* `pg`-type symmetries via pure translations parallel to the glide axis;
* parallel glides as the finite `pg` / `pgg`-style glide lane;
* `pmg`-type perpendicular mirrors;
* `pgg`-type 180° rotations;
* explicit incompatibility of quarter-turn (`p4`-style) rotation;
* exact `B₂/C₂` wallpaper root section inside the projected `D₅` Weyl shadow;
* metric preservation of the displayed `O(5,5)` block lift.

This file is a ledger/readback surface only. It introduces no new structures and
claims no global crystallographic or bundle classification theorem beyond the
finite owner theorems already proved upstream.
-/

namespace WallpaperPin55SummaryLedger

open InfoGeometry.Canonical.KleinBottleWallpaper
open InfoGeometry.Canonical.WallpaperKleinBottleCartan
open InfoGeometry.Canonical.WallpaperPin55RootCrossSection

/-- `pg`-type translation symmetry: any translation parallel to the glide axis is compatible. -/
theorem pg_translation_lane (b : ℝ) :
    IsCompatibleSymmetry (trans_y b) :=
  trans_y_compatible b

/-- Parallel glides give the finite glide-compatible wallpaper lane. -/
theorem pg_or_pgg_parallel_glide_lane (d : ℝ) :
    IsCompatibleSymmetry (parallel_glide d) :=
  parallel_glide_compatible d

/-- `pgg`-type half-turn is Klein-compatible. -/
theorem pgg_half_turn_lane :
    IsCompatibleSymmetry rot_180 :=
  rot_180_compatible

/-- `pmg`-type perpendicular mirror is Klein-compatible. -/
theorem pmg_perpendicular_mirror_lane :
    IsCompatibleSymmetry mirror_perp :=
  mirror_perp_compatible

/-- `p4`-type quarter-turn is excluded from the Klein-compatible finite lane. -/
theorem quarter_turn_excluded :
    ¬ IsCompatibleSymmetry rot_90 :=
  rot_90_incompatible

/-- The visible finite wallpaper root system is exactly the displayed `B₂/C₂` section. -/
theorem visible_wallpaper_root_is_b2c2 (r : Fin 8) :
    IsWallpaperB2Root (wallpaperB2Root r) :=
  ⟨r, rfl⟩

/-- Each visible wallpaper root has an explicit `D₅` lift. -/
theorem visible_root_has_d5_lift (r : Fin 8) :
    projectRoot2 (pin55LiftOfWallpaperRoot r) = wallpaperB2Root r ∧
      IsD5Root (pin55LiftOfWallpaperRoot r) :=
  ⟨project_pin55LiftOfWallpaperRoot r, pin55LiftOfWallpaperRoot_isD5Root r⟩

/-- Each displayed wallpaper `D₄` symmetry has an explicit `D₅` cross-section lift. -/
theorem wallpaper_symmetry_has_d5_cross_section (g : Fin 8) :
    projectWeyl2 (weylD5CrossSection g) = wallpaperD4 g ∧
      (weylD5CrossSection g).transpose * weylD5CrossSection g = 1 :=
  ⟨weylD5CrossSection_projects_wallpaper g, weylD5CrossSection_orthogonal g⟩

/-- The displayed `D₅` cross-section preserves the split `O(5,5)` metric. -/
theorem cross_section_preserves_split_metric (g : Fin 8) :
    (o55BlockLift (weylD5CrossSection g)).transpose * splitMetric55 *
        o55BlockLift (weylD5CrossSection g) = splitMetric55 :=
  weylD5CrossSection_preserves_splitMetric55 g

/-- Compact finite ledger packet for the wallpaper/root/metric cross-section. -/
theorem wallpaper_pin55_summary_packet (g r : Fin 8) (b d : ℝ) :
    IsCompatibleSymmetry (trans_y b) ∧
      IsCompatibleSymmetry (parallel_glide d) ∧
      IsCompatibleSymmetry rot_180 ∧
      IsCompatibleSymmetry mirror_perp ∧
      ¬ IsCompatibleSymmetry rot_90 ∧
      IsWallpaperB2Root (wallpaperB2Root r) ∧
      projectRoot2 (pin55LiftOfWallpaperRoot r) = wallpaperB2Root r ∧
      IsD5Root (matVec5 (weylD5CrossSection g) (pin55LiftOfWallpaperRoot r)) ∧
      projectWeyl2 (weylD5CrossSection g) = wallpaperD4 g ∧
      (o55BlockLift (weylD5CrossSection g)).transpose * splitMetric55 *
          o55BlockLift (weylD5CrossSection g) = splitMetric55 := by
  exact ⟨pg_translation_lane b,
    pg_or_pgg_parallel_glide_lane d,
    pgg_half_turn_lane,
    pmg_perpendicular_mirror_lane,
    quarter_turn_excluded,
    visible_wallpaper_root_is_b2c2 r,
    project_pin55LiftOfWallpaperRoot r,
    weylD5CrossSection_preserves_lifted_d5_roots g r,
    weylD5CrossSection_projects_wallpaper g,
    weylD5CrossSection_preserves_splitMetric55 g⟩

end WallpaperPin55SummaryLedger
