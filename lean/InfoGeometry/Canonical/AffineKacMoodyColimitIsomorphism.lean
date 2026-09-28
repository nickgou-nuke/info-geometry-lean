import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Canonical.AffineKacMoodyColimitBracket

/-!
# Categorical Colimit Bridge for Affine Kac-Moody Algebra

This module completes the categorical colimit bridge by identifying the 
categorical `ModuleCat` colimit of the finite-mode stages with the explicit 
ambient directed supremum (`affineFiniteModeUnion`). 
-/

noncomputable section

namespace InfoGeometry.Canonical.AffineKacMoodyColimitBridge

open CategoryTheory CategoryTheory.Limits
open VirasoroProject InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit
open InfoGeometry.Canonical.AffineKacMoodyColimitBracket

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
variable {𝓰 : Type*} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable {Φ : LinearMap.BilinForm 𝕜 𝓰}
variable {hΦ : Φ.lieInvariant 𝓰} {hΦs : Φ.IsSymm}

/-- The image of the categorical colimit inside the full Kac-Moody algebra 
exactly equals the directed supremum of the finite mode stages. -/
theorem colimitMap_range_eq_union :
    LinearMap.range (affineFiniteModeColimitMap Φ hΦ hΦs).hom = 
      affineFiniteModeUnion Φ hΦ hΦs := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    have hrep := Concrete.colimit_exists_rep (affineFiniteModeDiagram Φ hΦ hΦs) X
    rcases hrep with ⟨N, y, rfl⟩
    have hstage := affineFiniteModeColimitMap_stage Φ hΦ hΦs N
    have hy : (affineFiniteModeColimitMap Φ hΦ hΦs).hom
      ((colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N).hom y) = y.1 := by
      exact congrArg (fun f => f.hom y) hstage
    rw [hy]
    apply le_iSup (fun N => affineFiniteModeStage Φ hΦ hΦs N) N
    exact y.2
  · apply iSup_le
    intro N X hX
    have hstage := affineFiniteModeColimitMap_stage Φ hΦ hΦs N
    let y : affineFiniteModeStage Φ hΦ hΦs N := ⟨X, hX⟩
    use (colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N).hom y
    exact congrArg (fun f => f.hom y) hstage

end InfoGeometry.Canonical.AffineKacMoodyColimitBridge
