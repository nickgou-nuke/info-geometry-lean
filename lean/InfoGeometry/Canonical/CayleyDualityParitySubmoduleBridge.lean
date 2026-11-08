import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CayleyDualityParityActionBridge
import InfoGeometry.Canonical.CayleyDualityUnitsBridge

/-!
# Native submodule transport for the two Klein packets

This consumer upgrades the pointwise sector-action lemmas to equalities of
`Submodule.map`.  It is an algebraic sector-permutation API only; no metric,
completion, KK-class, or physical identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyDualityParitySubmoduleBridge

open InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
open InfoGeometry.Canonical.CayleyPeirceKleinFourBridge
open InfoGeometry.Canonical.CayleyDualityParityActionBridge

abbrev Coord :=
  InfoGeometry.Canonical.CayleyPeirceKleinFourBridge.Coord
abbrev CoordEnd :=
  InfoGeometry.Canonical.CayleyPeirceKleinFourBridge.CoordEnd

private theorem map_eq_of_involution_maps
    {f : CoordEnd} (hf : f * f = 1)
    {S T : Submodule ℝ Coord}
    (hST : ∀ {x : Coord}, x ∈ S → f x ∈ T)
    (hTS : ∀ {x : Coord}, x ∈ T → f x ∈ S) :
    Submodule.map f S = T := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hST hx
  · intro y hy
    refine ⟨f y, hTS hy, ?_⟩
    have hfy := congrArg (fun A : CoordEnd => A y) hf
    simpa only [Module.End.mul_apply, Module.End.one_apply] using hfy

noncomputable def involutionRestrictedEquiv
    {f : CoordEnd} (hf : f * f = 1)
    {S T : Submodule ℝ Coord}
    (hST : ∀ {x : Coord}, x ∈ S → f x ∈ T)
    (hTS : ∀ {x : Coord}, x ∈ T → f x ∈ S) :
    S ≃ₗ[ℝ] T :=
  { toFun := fun x => ⟨f x, hST x.property⟩
    invFun := fun y => ⟨f y, hTS y.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      have hx := congrArg (fun A : CoordEnd => A (x : Coord)) hf
      simpa only [Module.End.mul_apply, Module.End.one_apply] using hx
    right_inv := by
      intro y
      apply Subtype.ext
      have hy := congrArg (fun A : CoordEnd => A (y : Coord)) hf
      simpa only [Module.End.mul_apply, Module.End.one_apply] using hy
    map_add' := by
      intro x y
      apply Subtype.ext
      simp
    map_smul' := by
      intro c x
      apply Subtype.ext
      simp }

noncomputable def cayleyConj_E_plus_plus_equiv :
    E_plus_plus ≃ₗ[ℝ] E_minus_minus :=
  involutionRestrictedEquiv cayleyConj_sq
    cayleyConj_maps_E_plus_plus_to_E_minus_minus
    cayleyConj_maps_E_minus_minus_to_E_plus_plus

noncomputable def cayleyConj_E_minus_minus_equiv :
    E_minus_minus ≃ₗ[ℝ] E_plus_plus :=
  involutionRestrictedEquiv cayleyConj_sq
    cayleyConj_maps_E_minus_minus_to_E_plus_plus
    cayleyConj_maps_E_plus_plus_to_E_minus_minus

noncomputable def cayleyConj_E_plus_minus_equiv :
    E_plus_minus ≃ₗ[ℝ] E_plus_minus :=
  involutionRestrictedEquiv cayleyConj_sq
    cayleyConj_preserves_E_plus_minus cayleyConj_preserves_E_plus_minus

noncomputable def cayleyConj_E_minus_plus_equiv :
    E_minus_plus ≃ₗ[ℝ] E_minus_plus :=
  involutionRestrictedEquiv cayleyConj_sq
    cayleyConj_preserves_E_minus_plus cayleyConj_preserves_E_minus_plus

noncomputable def hodgeStar_E_plus_plus_equiv :
    E_plus_plus ≃ₗ[ℝ] E_minus_minus :=
  involutionRestrictedEquiv hodgeStar_sq
    hodgeStar_maps_E_plus_plus_to_E_minus_minus
    hodgeStar_maps_E_minus_minus_to_E_plus_plus

noncomputable def hodgeStar_E_minus_minus_equiv :
    E_minus_minus ≃ₗ[ℝ] E_plus_plus :=
  involutionRestrictedEquiv hodgeStar_sq
    hodgeStar_maps_E_minus_minus_to_E_plus_plus
    hodgeStar_maps_E_plus_plus_to_E_minus_minus

noncomputable def hodgeStar_E_plus_minus_equiv :
    E_plus_minus ≃ₗ[ℝ] E_minus_plus :=
  involutionRestrictedEquiv hodgeStar_sq
    hodgeStar_maps_E_plus_minus_to_E_minus_plus
    hodgeStar_maps_E_minus_plus_to_E_plus_minus

noncomputable def hodgeStar_E_minus_plus_equiv :
    E_minus_plus ≃ₗ[ℝ] E_plus_minus :=
  involutionRestrictedEquiv hodgeStar_sq
    hodgeStar_maps_E_minus_plus_to_E_plus_minus
    hodgeStar_maps_E_plus_minus_to_E_minus_plus

noncomputable def middleExchangeFlip_E_plus_plus_equiv :
    E_plus_plus ≃ₗ[ℝ] E_plus_plus :=
  involutionRestrictedEquiv middleExchangeFlip_sq
    middleExchangeFlip_preserves_E_plus_plus middleExchangeFlip_preserves_E_plus_plus

noncomputable def middleExchangeFlip_E_minus_minus_equiv :
    E_minus_minus ≃ₗ[ℝ] E_minus_minus :=
  involutionRestrictedEquiv middleExchangeFlip_sq
    middleExchangeFlip_preserves_E_minus_minus middleExchangeFlip_preserves_E_minus_minus

noncomputable def middleExchangeFlip_E_plus_minus_equiv :
    E_plus_minus ≃ₗ[ℝ] E_minus_plus :=
  involutionRestrictedEquiv middleExchangeFlip_sq
    middleExchangeFlip_maps_E_plus_minus_to_E_minus_plus
    middleExchangeFlip_maps_E_minus_plus_to_E_plus_minus

noncomputable def middleExchangeFlip_E_minus_plus_equiv :
    E_minus_plus ≃ₗ[ℝ] E_plus_minus :=
  involutionRestrictedEquiv middleExchangeFlip_sq
    middleExchangeFlip_maps_E_minus_plus_to_E_plus_minus
    middleExchangeFlip_maps_E_plus_minus_to_E_minus_plus

theorem cayleyConj_map_E_plus_plus :
    Submodule.map cayleyConj E_plus_plus = E_minus_minus := by
  apply map_eq_of_involution_maps cayleyConj_sq
  · exact cayleyConj_maps_E_plus_plus_to_E_minus_minus
  · exact cayleyConj_maps_E_minus_minus_to_E_plus_plus

theorem cayleyConj_map_E_minus_minus :
    Submodule.map cayleyConj E_minus_minus = E_plus_plus := by
  apply map_eq_of_involution_maps cayleyConj_sq
  · exact cayleyConj_maps_E_minus_minus_to_E_plus_plus
  · exact cayleyConj_maps_E_plus_plus_to_E_minus_minus

theorem cayleyConj_map_E_plus_minus :
    Submodule.map cayleyConj E_plus_minus = E_plus_minus := by
  apply map_eq_of_involution_maps cayleyConj_sq
  · exact cayleyConj_preserves_E_plus_minus
  · exact cayleyConj_preserves_E_plus_minus

theorem cayleyConj_map_E_minus_plus :
    Submodule.map cayleyConj E_minus_plus = E_minus_plus := by
  apply map_eq_of_involution_maps cayleyConj_sq
  · exact cayleyConj_preserves_E_minus_plus
  · exact cayleyConj_preserves_E_minus_plus

theorem hodgeStar_map_E_plus_plus :
    Submodule.map hodgeStar E_plus_plus = E_minus_minus := by
  apply map_eq_of_involution_maps hodgeStar_sq
  · exact hodgeStar_maps_E_plus_plus_to_E_minus_minus
  · exact hodgeStar_maps_E_minus_minus_to_E_plus_plus

theorem hodgeStar_map_E_minus_minus :
    Submodule.map hodgeStar E_minus_minus = E_plus_plus := by
  apply map_eq_of_involution_maps hodgeStar_sq
  · exact hodgeStar_maps_E_minus_minus_to_E_plus_plus
  · exact hodgeStar_maps_E_plus_plus_to_E_minus_minus

theorem hodgeStar_map_E_plus_minus :
    Submodule.map hodgeStar E_plus_minus = E_minus_plus := by
  apply map_eq_of_involution_maps hodgeStar_sq
  · exact hodgeStar_maps_E_plus_minus_to_E_minus_plus
  · exact hodgeStar_maps_E_minus_plus_to_E_plus_minus

theorem hodgeStar_map_E_minus_plus :
    Submodule.map hodgeStar E_minus_plus = E_plus_minus := by
  apply map_eq_of_involution_maps hodgeStar_sq
  · exact hodgeStar_maps_E_minus_plus_to_E_plus_minus
  · exact hodgeStar_maps_E_plus_minus_to_E_minus_plus

theorem middleExchangeFlip_map_E_plus_plus :
    Submodule.map middleExchangeFlip E_plus_plus = E_plus_plus := by
  apply map_eq_of_involution_maps middleExchangeFlip_sq
  · exact middleExchangeFlip_preserves_E_plus_plus
  · exact middleExchangeFlip_preserves_E_plus_plus

theorem middleExchangeFlip_map_E_minus_minus :
    Submodule.map middleExchangeFlip E_minus_minus = E_minus_minus := by
  apply map_eq_of_involution_maps middleExchangeFlip_sq
  · exact middleExchangeFlip_preserves_E_minus_minus
  · exact middleExchangeFlip_preserves_E_minus_minus

theorem middleExchangeFlip_map_E_plus_minus :
    Submodule.map middleExchangeFlip E_plus_minus = E_minus_plus := by
  apply map_eq_of_involution_maps middleExchangeFlip_sq
  · exact middleExchangeFlip_maps_E_plus_minus_to_E_minus_plus
  · exact middleExchangeFlip_maps_E_minus_plus_to_E_plus_minus

theorem middleExchangeFlip_map_E_minus_plus :
    Submodule.map middleExchangeFlip E_minus_plus = E_plus_minus := by
  apply map_eq_of_involution_maps middleExchangeFlip_sq
  · exact middleExchangeFlip_maps_E_minus_plus_to_E_plus_minus
  · exact middleExchangeFlip_maps_E_plus_minus_to_E_minus_plus

end InfoGeometry.Canonical.CayleyDualityParitySubmoduleBridge
