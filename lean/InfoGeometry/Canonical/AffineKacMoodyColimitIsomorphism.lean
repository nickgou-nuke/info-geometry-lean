import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit
import InfoGeometry.Canonical.AffineKacMoodyColimitBracket

open CategoryTheory CategoryTheory.Limits
open VirasoroProject InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

universe u
variable {𝕜 : Type u} [Field 𝕜] [CharZero 𝕜]
variable {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

noncomputable def unionCocone : Cocone (affineFiniteModeDiagram Φ hΦ hΦs) where
  pt := ModuleCat.of 𝕜 (affineFiniteModeUnion Φ hΦ hΦs)
  ι := {
    app := fun N => 
      let inc := Submodule.inclusion (le_iSup (fun N => affineFiniteModeStage Φ hΦ hΦs N) N)
      ModuleCat.ofHom inc
    naturality := fun N M h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
  }

theorem colimitMap_range_eq_union :
    LinearMap.range (affineFiniteModeColimitMap Φ hΦ hΦs).hom = 
      affineFiniteModeUnion Φ hΦ hΦs := by
  apply le_antisymm
  · -- range colimitMap ⊆ union
    let f := colimit.desc (affineFiniteModeDiagram Φ hΦ hΦs) (unionCocone Φ hΦ hΦs)
    have h_fac : f ≫ ModuleCat.ofHom (Submodule.subtype (affineFiniteModeUnion Φ hΦ hΦs)) = (affineFiniteModeColimitMap Φ hΦ hΦs) := by
      apply colimit.hom_ext
      intro j
      have h1 : (unionCocone Φ hΦ hΦs).ι.app j ≫ ModuleCat.ofHom (Submodule.subtype (affineFiniteModeUnion Φ hΦ hΦs)) = (affineFiniteModeCocone Φ hΦ hΦs).ι.app j := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl
      have h2 : colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) j ≫ (affineFiniteModeColimitMap Φ hΦ hΦs) = (affineFiniteModeCocone Φ hΦ hΦs).ι.app j := affineFiniteModeColimitMap_stage Φ hΦ hΦs j
      rw [← Category.assoc, colimit.ι_desc, h1, h2]
    intro x hx
    rcases hx with ⟨y, rfl⟩
    have h_eval : (Submodule.subtype (affineFiniteModeUnion Φ hΦ hΦs)) (f.hom y) = (affineFiniteModeColimitMap Φ hΦ hΦs).hom y := by
      exact congrArg (fun F => ModuleCat.Hom.hom F y) h_fac
    rw [← h_eval]
    exact Subtype.mem (f.hom y)
  · -- union ⊆ range colimitMap
    apply iSup_le
    intro N X hX
    have hstage := affineFiniteModeColimitMap_stage Φ hΦ hΦs N
    let y : affineFiniteModeStage Φ hΦ hΦs N := ⟨X, hX⟩
    use (colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N).hom y
    exact congrArg (fun F => ModuleCat.Hom.hom F y) hstage
