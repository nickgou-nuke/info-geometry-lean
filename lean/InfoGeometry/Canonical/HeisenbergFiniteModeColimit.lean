import InfoGeometry.Canonical.HeisenbergFiniteModeStages
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The filtered finite-mode colimit map for the Heisenberg algebra

Finite subsets of the standard `Jₖ,K` basis form a filtered diagram of
submodules. The canonical cocone into the full central extension therefore
induces a genuine `ModuleCat` colimit map.

This owner proves its stage law and constructs a linear equivalence to the
full carrier.  Topological and C⋆-completion statements are separate.
-/

noncomputable section

namespace InfoGeometry.Canonical

open CategoryTheory CategoryTheory.Limits
open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

noncomputable def heisenbergFiniteModeDiagram :
    Finset (Option ℤ) ⥤ ModuleCat 𝕜 where
  obj s := ModuleCat.of 𝕜 (heisenbergFiniteModeStage (𝕜 := 𝕜) s)
  map := by
    intro s t f
    have hst : s ≤ t := f.down.down
    exact ModuleCat.ofHom <|
      Submodule.inclusion (by
        apply Submodule.span_mono
        rintro x ⟨i, hi, rfl⟩
        exact ⟨i, ⟨hst hi, rfl⟩⟩)
  map_id s := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

noncomputable def heisenbergFiniteModeCocone :
    Cocone (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) where
  pt := ModuleCat.of 𝕜 (HeisenbergAlgebra 𝕜)
  ι := {
    app := fun s => ModuleCat.ofHom (Submodule.subtype _)
    naturality := by
      intro s t f
      ext x
      rfl }

abbrev heisenbergFiniteModeColimit : ModuleCat 𝕜 :=
  colimit (heisenbergFiniteModeDiagram (𝕜 := 𝕜))

noncomputable def heisenbergFiniteModeColimitMap :
    heisenbergFiniteModeColimit (𝕜 := 𝕜) ⟶
      ModuleCat.of 𝕜 (HeisenbergAlgebra 𝕜) :=
  colimit.desc _ (heisenbergFiniteModeCocone (𝕜 := 𝕜))

theorem heisenbergFiniteModeColimitMap_stage (s : Finset (Option ℤ)) :
    colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s ≫
        heisenbergFiniteModeColimitMap (𝕜 := 𝕜) =
      (heisenbergFiniteModeCocone (𝕜 := 𝕜)).ι.app s := by
  exact colimit.ι_desc _ _

theorem heisenbergFiniteModeColimitMap_surjective :
    Function.Surjective
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom := by
  intro X
  rcases heisenberg_mem_finiteModeStage (𝕜 := 𝕜) X with ⟨s, hX⟩
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s := ⟨X, hX⟩
  refine ⟨(colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x, ?_⟩
  change (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
      ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X
  have hstage := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s
  have hstage' := congrArg (fun f => f.hom) hstage
  exact congrArg (fun f => f x) hstage'

theorem heisenbergFiniteModeColimitMap_injective :
    Function.Injective
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom := by
  let F := heisenbergFiniteModeDiagram (𝕜 := 𝕜)
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat 𝕜)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits
      (forget (ModuleCat 𝕜))
  letI : PreservesColimit F (forget (ModuleCat 𝕜)) :=
    PreservesColimitsOfShape.preservesColimit
  intro x y hxy
  obtain ⟨s, a, hxa⟩ := Concrete.colimit_exists_rep F x
  obtain ⟨t, b, hby⟩ := Concrete.colimit_exists_rep F y
  rw [← hxa, ← hby] at hxy
  have hxy' :
      (heisenbergFiniteModeCocone (𝕜 := 𝕜)).ι.app s a =
        (heisenbergFiniteModeCocone (𝕜 := 𝕜)).ι.app t b := by
    have hs := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s
    have ht := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) t
    have hs' := congrArg (fun f => f.hom a) hs
    have ht' := congrArg (fun f => f.hom b) ht
    exact hs'.symm.trans (hxy.trans ht')
  let k := s ∪ t
  let f : s ⟶ k := ⟨PLift.up Finset.subset_union_left⟩
  let g : t ⟶ k := ⟨PLift.up Finset.subset_union_right⟩
  have hfg : F.map f a = F.map g b := by
    apply Subtype.ext
    exact hxy'
  have hcol :
      colimit.ι F s a = colimit.ι F t b :=
    Concrete.colimit_rep_eq_of_exists F a b ⟨k, f, g, hfg⟩
  exact hxa.symm.trans (hcol.trans hby)

theorem heisenbergFiniteModeColimitMap_bijective :
    Function.Bijective
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom :=
  ⟨heisenbergFiniteModeColimitMap_injective (𝕜 := 𝕜),
    heisenbergFiniteModeColimitMap_surjective (𝕜 := 𝕜)⟩

noncomputable def heisenbergFiniteModeColimitEquiv :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) ≃ₗ[𝕜]
      HeisenbergAlgebra 𝕜 :=
  LinearEquiv.ofBijective
    (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
    (heisenbergFiniteModeColimitMap_bijective (𝕜 := 𝕜))

end InfoGeometry.Canonical
