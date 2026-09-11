import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Endomorphisms transported through TopCat colimits

Given a natural endomorphism of a topological diagram, this owner constructs
the induced endomorphism of its colimit by the universal property.  It is a
pure categorical bridge: no analytic completion or C*-algebra structure is
assumed.
-/

namespace InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {J : Type*} [Category J]
variable (F : J ⥤ TopCat) [HasColimit F]

noncomputable def induced (η : F ⟶ F) :
    colimit F ⟶ colimit F :=
  colimit.desc F
    { pt := colimit F
      ι :=
        { app := fun j => η.app j ≫ colimit.ι F j
          naturality := by
            intro i j f
            simp only [Functor.const_obj_map, Category.assoc]
            rw [← Category.assoc, η.naturality f, Category.assoc]
            exact congrArg (fun q => η.app i ≫ q)
              ((colimit.cocone F).w f) } }

theorem induced_on_stage (η : F ⟶ F) (j : J) :
    colimit.ι F j ≫ induced F η =
      η.app j ≫ colimit.ι F j := by
  exact colimit.ι_desc _ j

theorem induced_unique (η : F ⟶ F) (g : colimit F ⟶ colimit F)
    (h : ∀ j : J, colimit.ι F j ≫ g =
      η.app j ≫ colimit.ι F j) :
    g = induced F η := by
  apply colimit.hom_ext
  intro j
  rw [h j, induced_on_stage]

theorem induced_id :
    induced F (𝟙 F) = 𝟙 (colimit F) := by
  apply colimit.hom_ext
  intro j
  rw [induced_on_stage]
  simp

theorem induced_comp (η θ : F ⟶ F) :
    induced F η ≫ induced F θ =
      induced F (η ≫ θ) := by
  apply colimit.hom_ext
  intro j
  calc
    colimit.ι F j ≫ induced F η ≫ induced F θ =
        (colimit.ι F j ≫ induced F η) ≫ induced F θ :=
      (Category.assoc _ _ _).symm
    _ = (η.app j ≫ colimit.ι F j) ≫ induced F θ := by
      rw [induced_on_stage]
    _ = η.app j ≫ (colimit.ι F j ≫ induced F θ) :=
      Category.assoc _ _ _
    _ = η.app j ≫ (θ.app j ≫ colimit.ι F j) := by
      rw [induced_on_stage]
    _ = (η.app j ≫ θ.app j) ≫ colimit.ι F j :=
      (Category.assoc _ _ _).symm
    _ = colimit.ι F j ≫ induced F (η ≫ θ) := by
      rw [induced_on_stage]
      rfl

theorem induced_involutive (η : F ⟶ F)
    (hη : η ≫ η = 𝟙 F) :
    induced F η ≫ induced F η = 𝟙 (colimit F) := by
  rw [induced_comp, hη, induced_id]

noncomputable def inducedIso (η θ : F ⟶ F)
    (hηθ : η ≫ θ = 𝟙 F)
    (hθη : θ ≫ η = 𝟙 F) :
    colimit F ≅ colimit F where
  hom := induced F η
  inv := induced F θ
  hom_inv_id := by
    rw [induced_comp, hηθ, induced_id]
  inv_hom_id := by
    rw [induced_comp, hθη, induced_id]

theorem inducedIso_symm (η θ : F ⟶ F)
    (hηθ : η ≫ θ = 𝟙 F)
    (hθη : θ ≫ η = 𝟙 F) :
    (inducedIso F η θ hηθ hθη).symm =
      inducedIso F θ η hθη hηθ := by
  apply Iso.ext
  rfl

end
end InfoGeometry.Canonical.TopCatColimitCompatibleEndomorphism
