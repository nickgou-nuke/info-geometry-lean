/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Categorical.ColimitComparison

/-!
# Orientation closure for canonical colimit comparisons

The canonical comparison between two colimit presentations has an inverse whose
underlying morphism is the canonical comparison in the reverse direction.  The
result is proved from the stage equations, so it does not add a second carrier
or package an isomorphism as input.
-/

namespace InfoGeometry.Categorical.ColimitComparison

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

variable {J : Type u₁} [Category.{v₁, u₁} J]
variable {C : Type u₂} [Category.{v₂, u₂} C]
variable {F : J ⥤ C}

/-- The inverse of the canonical comparison is the canonical comparison in the
reverse direction. -/
theorem isoOfIsColimit_inv_eq_reverse_hom
    {t₁ t₂ : Cocone F}
    (h₁ : IsColimit t₁) (h₂ : IsColimit t₂) :
    (isoOfIsColimit h₁ h₂).inv =
      (isoOfIsColimit h₂ h₁).hom := by
  apply h₂.hom_ext
  intro j
  exact (isoOfIsColimit_inv_fac h₁ h₂ j).trans
    (isoOfIsColimit_hom_fac h₂ h₁ j).symm

/-- The forward morphism is likewise the inverse comparison's reverse inverse.
This is the opposite orientation of `isoOfIsColimit_inv_eq_reverse_hom`. -/
theorem isoOfIsColimit_hom_eq_reverse_inv
    {t₁ t₂ : Cocone F}
    (h₁ : IsColimit t₁) (h₂ : IsColimit t₂) :
    (isoOfIsColimit h₁ h₂).hom =
      (isoOfIsColimit h₂ h₁).inv := by
  apply h₁.hom_ext
  intro j
  exact (isoOfIsColimit_hom_fac h₁ h₂ j).trans
    (isoOfIsColimit_inv_fac h₂ h₁ j).symm

end InfoGeometry.Categorical.ColimitComparison
