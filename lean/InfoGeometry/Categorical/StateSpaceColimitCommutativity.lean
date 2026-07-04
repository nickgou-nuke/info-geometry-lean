import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

noncomputable section

open CategoryTheory Limits

namespace InfoGeometry.Categorical.Holonomy

variable {C : Type*} [Category C]
variable {J : Type*} [Category J] [FinCategory J]
variable {I : Type*} [Category I] [IsFiltered I]
variable [HasLimitsOfShape J C] [HasColimitsOfShape I C]
variable [PreservesLimitsOfShape J (colim : (I ⥤ C) ⥤ _)]

/-- Filtered colimits commute with finite limits. -/
noncomputable def filtered_colimit_commutes_finite_limit_iso (F_diag : J ⥤ I ⥤ C) :
    colimit (limit F_diag) ≅ limit (colimit F_diag.flip) := by
  exact colimitLimitIso (F := F_diag)

universe u

variable (R : Type u) [CommRing R]
variable {J₀ : Type u} [SmallCategory J₀] [FinCategory J₀]
variable {I₀ : Type u} [SmallCategory I₀] [IsFiltered I₀]

/--
The two functor-composition spellings of applying the limit functor to a
`J`-indexed family of `I`-diagrams induce the same colimit object.

In Lean, `lim ∘ F_diag` is function composition and is not a functor. The
functor-level spelling is `Functor.comp F_diag lim`, definitionally equal to
`F_diag ⋙ lim`.
-/
noncomputable def limCompositionNatIso (F_diag : J₀ ⥤ I₀ ⥤ ModuleCat.{u} R) :
    (F_diag ⋙ lim) ≅ Functor.comp F_diag lim :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (by simp)

noncomputable def lim_composition_naturality (F_diag : J₀ ⥤ I₀ ⥤ ModuleCat.{u} R) :
    colimit (F_diag ⋙ lim) ≅ colimit (Functor.comp F_diag lim) := by
  exact HasColimit.isoOfNatIso (limCompositionNatIso R F_diag)

/--
Module-category specialization of mathlib's filtered-colimit/finite-limit
interchange theorem.

This is the grounded form of the AI-Studio "colimit/limit iso" proposal: a
finite `J₀`-limit commutes with an `I₀`-filtered colimit in `ModuleCat`.
-/
noncomputable def colimit_limit_iso (F_diag : J₀ ⥤ I₀ ⥤ ModuleCat.{u} R) :
    colimit (limit F_diag) ≅ limit (colimit F_diag.flip) := by
  letI : PreservesLimitsOfShape J₀ (colim : (I₀ ⥤ ModuleCat.{u} R) ⥤ _) :=
    filtered_colim_preservesFiniteLimits
  exact colimitLimitIso (F := F_diag)

end InfoGeometry.Categorical.Holonomy
