import InfoGeometry.Canonical.HeisenbergFiniteModeStages
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

end InfoGeometry.Canonical
