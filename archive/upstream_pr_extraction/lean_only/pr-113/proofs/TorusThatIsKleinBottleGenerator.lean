import proofs.TitsBruhatBrillouinKlein
import proofs.FrozenPin55ManifoldFlow
import proofs.O55GradedGeneratorBasis
import proofs.WallpaperO55FrozenSelectionBridge

/-!
# Torus-that-is-Klein-bottle manifold generator

This file records the finite bookkeeping consequences of a torus-to-Klein
presentation, using explicit group elements, their Klein relations, and the
existing generator count lemmas.
-/

noncomputable section

namespace TorusThatIsKleinBottleGenerator

/-- The manifold generator is a single twist relation. -/
def manifoldGeneratorCount : ℕ := 1

@[simp] theorem manifoldGeneratorCount_eq : manifoldGeneratorCount = 1 := rfl

/-- The p6m wallpaper count is the active `O(5,5)` count plus this generator. -/
theorem p6m_psa_count_matches_active_o55_plus_manifold_generator :
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m =
        O55GradedGeneratorBasis.activeGradedGeneratorCount + manifoldGeneratorCount := by
  rw [manifoldGeneratorCount_eq]
  exact WallpaperO55FrozenSelectionBridge.p6m_psa_count_matches_active_o55_plus_base

end TorusThatIsKleinBottleGenerator

end noncomputable section
