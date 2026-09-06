import proofs.ChiralConeAlgebraFinality
import proofs.MorandiWallpaperCohomology
import proofs.ProjectiveWallpaperGaugePSA
import proofs.FixedLineRiemannKlein
import proofs.ColorConfinementGNS

/-!
# Wallpaper holographic selection rules

Thin capstone over existing modules.  It does **not** reprove the chiral cone,
wallpaper classification, glide/Klein, or S₃/GNS confinement scaffolds.  It
packages them as closed finite selection-rule facts:

```text
local M₂(C) chiral tile
  → wallpaper/glide finite selection rules
  → S₃/Weyl + GNS trace projection
```

Important separation:

* `pg` is the non-symmorphic glide layer compatible with a Klein quotient;
* `p6m` is the hexagonal/color-root wallpaper layer whose point-group shadow is
  read through the existing S₃/Weyl/GNS modules.
-/

noncomputable section

namespace WallpaperHolographicSelectionRules

/-! ## Closed finite wallpaper kernel -/

/-- The `pg` and `p6m` wallpaper groups are distinct layers in the finite IUCr
list: glide/Klein versus hexagonal color-root selection. -/
theorem pg_p6m_are_distinct :
    ProjectiveWallpaperGaugePSA.WallpaperGroup.pg ≠
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m := by
  decide

/-- The `pg` projective-cohomology exponent is the glide/fractional-translation
small layer in the PSA table. -/
theorem pg_H2Exponent :
    ProjectiveWallpaperGaugePSA.H2Exponent
      ProjectiveWallpaperGaugePSA.WallpaperGroup.pg = 1 := rfl

/-- The `p6m` exponent marks the richer hexagonal/projective color-crystal
selection layer in the PSA table. -/
theorem p6m_H2Exponent :
    ProjectiveWallpaperGaugePSA.H2Exponent
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m = 4 := rfl

/-- The `p6m` non-equivalent projective symmetry algebra count from the table. -/
theorem p6m_nonEquivalentPSACount :
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m = 16 := rfl

/-- The finite wallpaper/GNS package: 17 wallpaper groups, `pg`
glide extinction, distinct `pg`/`p6m` roles, S₃/GNS color selection, and the
local chiral `M₂(C)` tile facts. -/
theorem wallpaper_holographic_selection_rule_finite_kernel :
    MorandiWallpaperCohomology.wallpaperNames.length = 17 ∧
    MorandiWallpaperCohomology.morandiWallpaperCount = 17 ∧
    ProjectiveWallpaperGaugePSA.allWallpaperGroups.length = 17 ∧
    ProjectiveWallpaperGaugePSA.H2Exponent
      ProjectiveWallpaperGaugePSA.WallpaperGroup.pg = 1 ∧
    ProjectiveWallpaperGaugePSA.H2Exponent
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m = 4 ∧
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m = 16 ∧
    ProjectiveWallpaperGaugePSA.WallpaperGroup.pg ≠
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m ∧
    (∀ {k : ℕ} {c : ℂ}, Odd k → c = FixedLineRiemannKlein.pgPhase k * c → c = 0) ∧
    ChiralConeAlgebraFinality.sPlus * ChiralConeAlgebraFinality.sPlus = 0 ∧
    ChiralConeAlgebraFinality.sMinus * ChiralConeAlgebraFinality.sMinus = 0 ∧
    ChiralConeAlgebraFinality.NPlus + ChiralConeAlgebraFinality.NMinus =
      (1 : ChiralConeAlgebraFinality.M2C) ∧
    ChiralConeAlgebraFinality.τ ChiralConeAlgebraFinality.NPlus = 1 / 2 ∧
    ChiralConeAlgebraFinality.τ ChiralConeAlgebraFinality.NMinus = 1 / 2 ∧
    ((2 : ℂ)*1 + (0 : ℂ)*1 + (1 : ℂ)*2 = (4 : ℂ) ∧
      (3 : ℂ) ≠ (4 : ℂ) ∧
      WeylSU3ColorSymmetry.swap12 ∘ WeylSU3ColorSymmetry.swap23 ∘
        WeylSU3ColorSymmetry.swap12 =
        WeylSU3ColorSymmetry.swap23 ∘ WeylSU3ColorSymmetry.swap12 ∘
          WeylSU3ColorSymmetry.swap23 ∧
      (1 : ℂ)^2 + (1 : ℂ)^2 + (2 : ℂ)^2 = (6 : ℂ)) := by
  rcases ChiralConeAlgebraFinality.thermal_self_dual_occupations with
    ⟨hTauPlus, hTauMinus, _hTauUnit⟩
  exact ⟨MorandiWallpaperCohomology.wallpaperNames_length,
    MorandiWallpaperCohomology.morandiWallpaperCount_eq_17,
    ProjectiveWallpaperGaugePSA.allWallpaperGroups_length,
    pg_H2Exponent,
    p6m_H2Exponent,
    p6m_nonEquivalentPSACount,
    pg_p6m_are_distinct,
    FixedLineRiemannKlein.pg_fixed_line_extinction,
    ChiralConeAlgebraFinality.sPlus_sq_zero,
    ChiralConeAlgebraFinality.sMinus_sq_zero,
    ChiralConeAlgebraFinality.chiral_projector_completeness,
    hTauPlus,
    hTauMinus,
    ColorConfinementGNS.color_confinement_gns_synthesis⟩

end WallpaperHolographicSelectionRules

end noncomputable section
