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

section ModuleDiagramLimits

variable {I₁ : Type u} [SmallCategory I₁]
variable {K₁ : Type u} [SmallCategory K₁]

/-- The descended map agrees with every local operator on its stage. -/
@[reassoc]
theorem stageInjection_desc
    (F : I₁ ⥤ ModuleCat.{u} R) (t : Cocone F) (i : I₁) :
    colimit.ι F i ≫ colimit.desc F t = t.ι.app i := by
  exact colimit.ι_desc t i

/-- A compatible family of algebraic states on a module diagram.

Naturality says precisely that a state at a later stage restricts along every
structure map to the state at the earlier stage.
-/
abbrev CompatibleStateFamily
    (F : I₁ ⥤ ModuleCat.{u} R) :=
  F ⟶ (Functor.const I₁).obj (ModuleCat.of R R)

/-- Algebraic states on a colimit are equivalent to compatible families of
algebraic states on all stages.

This is the precise categorical content of
`Hom(CategoryTheory.Limits.colimit F, R) ≃ limit_i Hom(F i, R)`. It concerns all `R`-linear
functionals. Positivity, normalization, continuity, and the KMS condition are
additional structures or predicates and are not asserted by this equivalence.
-/
noncomputable def colimitStateEquivCompatibleFamily
    (F : I₁ ⥤ ModuleCat.{u} R) :
    (CategoryTheory.Limits.colimit F ⟶ ModuleCat.of R R) ≃
      CompatibleStateFamily R F :=
  (colimit.isColimit F).homEquiv (W := ModuleCat.of R R)

/-- Restricting a global algebraic state to stage `i` is composition with the
canonical stage injection. -/
@[simp]
theorem colimitStateEquivCompatibleFamily_apply_app
    (F : I₁ ⥤ ModuleCat.{u} R)
    (φ : CategoryTheory.Limits.colimit F ⟶ ModuleCat.of R R) (i : I₁) :
    (colimitStateEquivCompatibleFamily R F φ).app i =
      colimit.ι F i ≫ φ := by
  rfl

/-- Gluing a compatible family and then restricting to a stage recovers the
original stage state. -/
@[simp, reassoc]
theorem colimitStateEquivCompatibleFamily_symm_app
    (F : I₁ ⥤ ModuleCat.{u} R)
    (s : CompatibleStateFamily R F) (i : I₁) :
    colimit.ι F i ≫
        (colimitStateEquivCompatibleFamily R F).symm s =
      s.app i := by
  exact (colimit.isColimit F).ι_app_homEquiv_symm s i

/-- The lifted map recovers every component of the original cone. -/
@[reassoc]
theorem lift_stageProjection
    (G : K₁ ⥤ ModuleCat.{u} R) (t : Cone G) (k : K₁) :
    limit.lift G t ≫ limit.π G k = t.π.app k := by
  exact limit.lift_π t k

end ModuleDiagramLimits

variable {J₀ : Type u} [SmallCategory J₀] [FinCategory J₀]
variable {I₀ : Type u} [SmallCategory I₀] [IsFiltered I₀]

/-- Filtered colimits of modules preserve limits of every fixed finite shape.

This is the precise Mathlib form of exactness used by the interchange theorem;
`PreservesFiniteLimits` is not the type returned directly by the underlying
shape-indexed instance.
-/
noncomputable def filteredColimitPreservesFiniteLimitsOfShape :
    PreservesLimitsOfShape J₀
      (colim : (I₀ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R) :=
  filtered_colim_preservesFiniteLimits

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
    filteredColimitPreservesFiniteLimitsOfShape R
  exact colimitLimitIso (F := F_diag)

end InfoGeometry.Categorical.Holonomy
