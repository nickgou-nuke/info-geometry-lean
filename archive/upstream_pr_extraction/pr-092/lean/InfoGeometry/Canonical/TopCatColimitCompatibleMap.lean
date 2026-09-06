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

theorem inducedMap_id :
    inducedMap (𝟙 F) = 𝟙 (colimit F) := by
  apply colimit.hom_ext
  intro j
  rw [inducedMap_on_stage]
  simp

theorem inducedMap_comp
    {H : J ⥤ TopCat} [HasColimit H]
    (τ : F ⟶ G) (υ : G ⟶ H) :
    inducedMap (τ ≫ υ) = inducedMap τ ≫ inducedMap υ := by
  apply colimit.hom_ext
  intro j
  calc
    colimit.ι F j ≫ inducedMap (τ ≫ υ) =
        (τ ≫ υ).app j ≫ colimit.ι H j := inducedMap_on_stage (τ ≫ υ) j
    _ = (τ.app j ≫ υ.app j) ≫ colimit.ι H j := by rfl
    _ = τ.app j ≫ (υ.app j ≫ colimit.ι H j) := Category.assoc _ _ _
    _ = τ.app j ≫ (colimit.ι G j ≫ inducedMap υ) := by
      rw [inducedMap_on_stage]
    _ = (τ.app j ≫ colimit.ι G j) ≫ inducedMap υ :=
      (Category.assoc _ _ _).symm
    _ = (colimit.ι F j ≫ inducedMap τ) ≫ inducedMap υ := by
      rw [inducedMap_on_stage]
    _ = colimit.ι F j ≫ inducedMap τ ≫ inducedMap υ :=
      Category.assoc _ _ _

noncomputable def inducedMapIso (e : F ≅ G) :
    colimit F ≅ colimit G where
  hom := inducedMap e.hom
  inv := inducedMap e.inv
  hom_inv_id := by
    rw [← inducedMap_comp, e.hom_inv_id, inducedMap_id]
  inv_hom_id := by
    rw [← inducedMap_comp, e.inv_hom_id, inducedMap_id]

theorem inducedMapIso_trans
    {H : J ⥤ TopCat} [HasColimit H]
    (e : F ≅ G) (f : G ≅ H) :
    inducedMapIso (e.trans f) =
      (inducedMapIso e).trans (inducedMapIso f) := by
  apply Iso.ext
  exact inducedMap_comp e.hom f.hom

theorem inducedMapIso_refl :
    inducedMapIso (Iso.refl F) = Iso.refl (colimit F) := by
  apply Iso.ext
  exact inducedMap_id

theorem inducedMapIso_hom_on_stage (e : F ≅ G) (j : J) :
    colimit.ι F j ≫ (inducedMapIso e).hom =
      e.hom.app j ≫ colimit.ι G j := by
  exact inducedMap_on_stage e.hom j

theorem inducedMapIso_inv_on_stage (e : F ≅ G) (j : J) :
    colimit.ι G j ≫ (inducedMapIso e).inv =
      e.inv.app j ≫ colimit.ι F j := by
  exact inducedMap_on_stage e.inv j

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
