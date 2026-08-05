import InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism

/-!
# Transport of compatible TopCat actions through colimit maps

This owner constructs the colimit map induced by a natural transformation
between diagrams and proves the corresponding intertwining theorem for
compatible stagewise endomorphisms.
-/

namespace InfoGeometry.Canonical.TopCatColimitCompatibleMap

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism

noncomputable section

variable {J : Type*} [Category J]
variable {F G : J ⥤ TopCat} [HasColimit F] [HasColimit G]

noncomputable def inducedMap (τ : F ⟶ G) :
    colimit F ⟶ colimit G :=
  colimit.desc F
    { pt := colimit G
      ι :=
        { app := fun j => τ.app j ≫ colimit.ι G j
          naturality := by
            intro i j f
            simp only [Functor.const_obj_map, Category.assoc]
            rw [← Category.assoc, τ.naturality f, Category.assoc]
            exact congrArg (fun q => τ.app i ≫ q)
              ((colimit.cocone G).w f) } }

theorem inducedMap_on_stage (τ : F ⟶ G) (j : J) :
    colimit.ι F j ≫ inducedMap τ =
      τ.app j ≫ colimit.ι G j := by
  exact colimit.ι_desc _ j

theorem inducedMap_unique (τ : F ⟶ G) (h : colimit F ⟶ colimit G)
    (hh : ∀ j : J, colimit.ι F j ≫ h =
      τ.app j ≫ colimit.ι G j) :
    h = inducedMap τ := by
  apply colimit.hom_ext
  intro j
  rw [hh j, inducedMap_on_stage]

theorem inducedMap_intertwines
    (η : F ⟶ F) (θ : G ⟶ G) (τ : F ⟶ G)
    (hτ : η ≫ τ = τ ≫ θ) :
    induced F η ≫ inducedMap τ =
      inducedMap τ ≫ induced G θ := by
  apply colimit.hom_ext
  intro j
  calc
    colimit.ι F j ≫ induced F η ≫ inducedMap τ =
        (colimit.ι F j ≫ induced F η) ≫ inducedMap τ :=
      (Category.assoc _ _ _).symm
    _ = (η.app j ≫ colimit.ι F j) ≫ inducedMap τ := by
      rw [induced_on_stage]
    _ = η.app j ≫ (colimit.ι F j ≫ inducedMap τ) :=
      Category.assoc _ _ _
    _ = η.app j ≫ (τ.app j ≫ colimit.ι G j) := by
      rw [inducedMap_on_stage]
    _ = (τ.app j ≫ θ.app j) ≫ colimit.ι G j := by
      rw [← Category.assoc]
      exact congrArg (fun q => q ≫ colimit.ι G j)
        (congr_app hτ j)
    _ = τ.app j ≫ (θ.app j ≫ colimit.ι G j) :=
      Category.assoc _ _ _
    _ = τ.app j ≫ (colimit.ι G j ≫ induced G θ) := by
      rw [induced_on_stage]
    _ = (τ.app j ≫ colimit.ι G j) ≫ induced G θ :=
      (Category.assoc _ _ _).symm
    _ = (colimit.ι F j ≫ inducedMap τ) ≫ induced G θ := by
      rw [inducedMap_on_stage]
    _ = colimit.ι F j ≫ inducedMap τ ≫ induced G θ :=
      Category.assoc _ _ _

end
end InfoGeometry.Canonical.TopCatColimitCompatibleMap
