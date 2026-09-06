import proofs.WallpaperHolographicSelectionRules
import proofs.O55GradedGeneratorBasis

/-!
# Wallpaper-to-`O(5,5)` frozen selection bridge

This is the thin capstone connecting the wallpaper selection layer to the
frozen graded `O(5,5)` generator basis:

* `pg` remains the glide/Klein layer, represented in the frozen-flow picture by
  the mixed/sign-changing directions and frozen constraint;
* `p6m` remains the hexagonal/color layer, represented by active compact/boost
  generator parameters in the `O(5,5)` carrier;
* the finite arithmetic lines up as `p6m`'s non-equivalent PSA count
  `16 = 15 + 1`, where `15` is the active graded generator count after freezing
  four coordinates and `1` is the scalar/base channel.

The finite bridge is compiled.
-/

namespace WallpaperO55FrozenSelectionBridge

/-- The active `O(5,5)` generator count plus one scalar/base channel matches the
`p6m` non-equivalent PSA count in the wallpaper table. -/
theorem p6m_psa_count_matches_active_o55_plus_base :
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m =
        O55GradedGeneratorBasis.activeGradedGeneratorCount + 1 := by
  calc
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
        ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m = 16 :=
      WallpaperHolographicSelectionRules.p6m_nonEquivalentPSACount
    _ = 15 + 1 := by norm_num
    _ = O55GradedGeneratorBasis.activeGradedGeneratorCount + 1 := by
      rw [O55GradedGeneratorBasis.active_graded_generator_count_eq]

end WallpaperO55FrozenSelectionBridge
