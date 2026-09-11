import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Restriction-preserving morphisms of compatible readout families

This is the morphism layer for the induced compatible-family topology.  A
morphism acts by continuous linear maps at every finite stage and is required
to commute with the block restriction maps.  The construction remains a
readout-family interface; it does not assert a KMS or completed UHF theory.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism

open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNet
open InfoGeometry.Clifford.Cl11TensorTower

abbrev ReadoutSpace (n : ℕ) := MatStage n →L[ℝ] ℝ

def mapFamily
    (map : ∀ n : ℕ, ReadoutSpace n →L[ℝ] ReadoutSpace n)
    (map_compatibility :
      ∀ (ρ : ReadoutFamily),
        (∀ n : ℕ, (ρ n).comp (stageRestrictCLM n) = ρ (n + 1)) →
        ∀ n : ℕ,
          (map n (ρ n)).comp (stageRestrictCLM n) =
            map (n + 1) (ρ (n + 1)))
    (ρ : CompatibleContinuousReadoutFamily) :
    CompatibleContinuousReadoutFamily :=
  ⟨fun n => map n (ρ.1 n), map_compatibility ρ.1 ρ.2⟩

structure CompatibleReadoutFamilyMap where
  map : ∀ n : ℕ, ReadoutSpace n →L[ℝ] ReadoutSpace n
  map_compatibility :
    ∀ (ρ : ReadoutFamily),
      (∀ n : ℕ, (ρ n).comp (stageRestrictCLM n) = ρ (n + 1)) →
      ∀ n : ℕ,
        (map n (ρ n)).comp (stageRestrictCLM n) =
          map (n + 1) (ρ (n + 1))
  continuous_map :
    Continuous (mapFamily map map_compatibility)

@[simp] theorem mapFamily_apply
    (Φ : CompatibleReadoutFamilyMap)
    (ρ : CompatibleContinuousReadoutFamily) (n : ℕ) :
    (mapFamily Φ.map Φ.map_compatibility ρ).1 n = Φ.map n (ρ.1 n) := rfl

theorem mapFamily_compatible_apply
    (Φ : CompatibleReadoutFamilyMap)
    (ρ : CompatibleContinuousReadoutFamily) (n : ℕ)
    (X : MatStage (n + 1)) :
    (mapFamily Φ.map Φ.map_compatibility ρ).1 n
        (stageRestrict n X) =
      (mapFamily Φ.map Φ.map_compatibility ρ).1 (n + 1) X := by
  exact compatible_apply (mapFamily Φ.map Φ.map_compatibility ρ) n X

def toTopCatHom (Φ : CompatibleReadoutFamilyMap) :
    TopCat.of CompatibleContinuousReadoutFamily ⟶
      TopCat.of CompatibleContinuousReadoutFamily :=
  TopCat.ofHom
    { toFun := mapFamily Φ.map Φ.map_compatibility
      continuous_toFun := Φ.continuous_map }

@[simp] theorem toTopCatHom_apply
    (Φ : CompatibleReadoutFamilyMap)
    (ρ : CompatibleContinuousReadoutFamily) :
    toTopCatHom Φ ρ = mapFamily Φ.map Φ.map_compatibility ρ := rfl

end InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMorphism
