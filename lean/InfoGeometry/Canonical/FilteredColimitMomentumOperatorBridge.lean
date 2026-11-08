import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Data.Complex.Basic

/-!
# Native filtered-colimit transport of a stage operator family

For a diagram of modules, a compatible family of stage operators is a natural
transformation `η : F ⟶ F`.  Mathlib's `colim.map η` is then the canonical
operator on the filtered colimit.  This owner records the universal stage
intertwining and does not add any analytic completion or convergence claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredColimitMomentumOperatorBridge

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type u} [Category.{u} J]
variable (F : J ⥤ ModuleCat ℂ) [HasColimit F]

/-- The operator induced on the module colimit by a compatible stage family. -/
def colimitMomentum (η : F ⟶ F) : colimit F ⟶ colimit F :=
  colim.map η

@[simp, reassoc] theorem colimitMomentum_stage (η : F ⟶ F) (j : J) :
    colimit.ι F j ≫ colimitMomentum F η =
      η.app j ≫ colimit.ι F j := by
  exact colimit.ι_map η j

theorem colimitMomentum_unique (η : F ⟶ F) (f : colimit F ⟶ colimit F)
    (h : ∀ j, colimit.ι F j ≫ f = η.app j ≫ colimit.ι F j) :
    f = colimitMomentum F η := by
  apply (colimit.isColimit F).hom_ext
  intro j
  calc
    (colimit.cocone F).ι.app j ≫ f = η.app j ≫ colimit.ι F j := h j
    _ = (colimit.cocone F).ι.app j ≫ colimitMomentum F η := by
      symm
      exact colimitMomentum_stage F η j

@[simp] theorem colimitMomentum_id :
    colimitMomentum F (𝟙 F) = 𝟙 (colimit F) := by
  symm
  apply colimitMomentum_unique F (𝟙 F) (𝟙 (colimit F))
  intro j
  simp

theorem colimitMomentum_comp (η θ : F ⟶ F) :
    colimitMomentum F (η ≫ θ) =
      colimitMomentum F η ≫ colimitMomentum F θ := by
  symm
  apply colimitMomentum_unique F (η ≫ θ)
    (colimitMomentum F η ≫ colimitMomentum F θ)
  intro j
  calc
    colimit.ι F j ≫ colimitMomentum F η ≫ colimitMomentum F θ =
        (η.app j ≫ colimit.ι F j) ≫ colimitMomentum F θ := by
          rw [← Category.assoc, colimitMomentum_stage F η j]
    _ = η.app j ≫ (colimit.ι F j ≫ colimitMomentum F θ) := by
          rw [Category.assoc]
    _ = η.app j ≫ (θ.app j ≫ colimit.ι F j) := by
          rw [colimitMomentum_stage F θ j]
    _ = (η ≫ θ).app j ≫ colimit.ι F j := by
          rfl

end InfoGeometry.Canonical.FilteredColimitMomentumOperatorBridge
