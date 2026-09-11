import InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Composition laws for compatible readout-family morphisms

The restriction-preserving maps form a compositional layer.  The identities
below concern only the induced compatible-family topology and its `TopCat`
realization.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphismCategory

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNet

noncomputable def identity : CompatibleReadoutFamilyMap where
  map := fun n => ContinuousLinearMap.id ℝ (ReadoutSpace n)
  map_compatibility := by
    intro ρ hρ n
    exact hρ n
  continuous_map := by
    have hmap :
        mapFamily
            (fun n => ContinuousLinearMap.id ℝ (ReadoutSpace n))
            (by
              intro ρ hρ n
              exact hρ n) =
          (fun ρ : CompatibleContinuousReadoutFamily => ρ) := by
      funext ρ
      apply Subtype.ext
      funext n
      rfl
    rw [hmap]
    exact continuous_id

noncomputable def comp
    (Φ Ψ : CompatibleReadoutFamilyMap) :
    CompatibleReadoutFamilyMap where
  map := fun n => (Φ.map n).comp (Ψ.map n)
  map_compatibility := by
    intro ρ hρ n
    have hΨ :
        ∀ n : ℕ,
          (Ψ.map n (ρ n)).comp (stageRestrictCLM n) =
            Ψ.map (n + 1) (ρ (n + 1)) :=
      Ψ.map_compatibility ρ hρ
    have hΨfamily :
        ∀ n : ℕ,
          (Ψ.map n (ρ n)).comp (stageRestrictCLM n) =
            Ψ.map (n + 1) (ρ (n + 1)) := hΨ
    have hΦ := Φ.map_compatibility
      (fun n => Ψ.map n (ρ n)) hΨfamily n
    simpa only [ContinuousLinearMap.comp_apply] using hΦ
  continuous_map := by
    have hmap :
        mapFamily
            (fun n => (Φ.map n).comp (Ψ.map n))
            (by
              intro ρ hρ n
              have hΨ :
                  ∀ n : ℕ,
                    (Ψ.map n (ρ n)).comp (stageRestrictCLM n) =
                      Ψ.map (n + 1) (ρ (n + 1)) :=
                Ψ.map_compatibility ρ hρ
              have hΨfamily :
                  ∀ n : ℕ,
                    (Ψ.map n (ρ n)).comp (stageRestrictCLM n) =
                      Ψ.map (n + 1) (ρ (n + 1)) := hΨ
              exact Φ.map_compatibility
                (fun n => Ψ.map n (ρ n)) hΨfamily n) =
          (fun ρ => mapFamily Φ.map Φ.map_compatibility
            (mapFamily Ψ.map Ψ.map_compatibility ρ)) := by
      funext ρ
      apply Subtype.ext
      funext n
      rfl
    rw [hmap]
    exact Φ.continuous_map.comp Ψ.continuous_map

@[simp] theorem identity_map_apply
    (ρ : CompatibleContinuousReadoutFamily) :
    mapFamily identity.map identity.map_compatibility ρ = ρ := by
  apply Subtype.ext
  funext n
  rfl

@[simp] theorem comp_map_apply
    (Φ Ψ : CompatibleReadoutFamilyMap)
    (ρ : CompatibleContinuousReadoutFamily) :
    mapFamily (comp Φ Ψ).map (comp Φ Ψ).map_compatibility ρ =
      mapFamily Φ.map Φ.map_compatibility
        (mapFamily Ψ.map Ψ.map_compatibility ρ) := by
  apply Subtype.ext
  funext n
  rfl

theorem toTopCatHom_identity :
    toTopCatHom identity = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  change mapFamily identity.map identity.map_compatibility ρ = ρ
  exact identity_map_apply ρ

theorem toTopCatHom_comp
    (Φ Ψ : CompatibleReadoutFamilyMap) :
    toTopCatHom (comp Φ Ψ) =
      toTopCatHom Ψ ≫ toTopCatHom Φ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  change mapFamily (comp Φ Ψ).map (comp Φ Ψ).map_compatibility ρ =
    mapFamily Φ.map Φ.map_compatibility
      (mapFamily Ψ.map Ψ.map_compatibility ρ)
  exact comp_map_apply Φ Ψ ρ

end InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphismCategory
