/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Canonical comparison of colimit presentations

This module contains only the universal-property comparison layer. It does
not introduce a second colimit carrier: two cocones over the same diagram are
compared through their `IsColimit` witnesses.
-/

namespace InfoGeometry.Categorical.ColimitComparison

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

variable {J : Type u₁} [Category.{v₁, u₁} J]
variable {C : Type u₂} [Category.{v₂, u₂} C]
variable {F : J ⥤ C}

/-- The unique comparison isomorphism between two colimit cocones for the same
diagram. Both directions are universal descents supplied by the two
`IsColimit` witnesses. -/
noncomputable def isoOfIsColimit
    {t₁ t₂ : Cocone F} (h₁ : IsColimit t₁) (h₂ : IsColimit t₂) :
    t₁.pt ≅ t₂.pt :=
  { hom := h₁.desc t₂
    inv := h₂.desc t₁
    hom_inv_id := by
      apply h₁.hom_ext
      intro j
      calc
        t₁.ι.app j ≫ h₁.desc t₂ ≫ h₂.desc t₁ =
            (t₁.ι.app j ≫ h₁.desc t₂) ≫ h₂.desc t₁ := by
              rw [Category.assoc]
        _ = t₂.ι.app j ≫ h₂.desc t₁ := by rw [h₁.fac]
        _ = t₁.ι.app j := h₂.fac t₁ j
        _ = t₁.ι.app j ≫ 𝟙 _ := by simp
    inv_hom_id := by
      apply h₂.hom_ext
      intro j
      calc
        t₂.ι.app j ≫ h₂.desc t₁ ≫ h₁.desc t₂ =
            (t₂.ι.app j ≫ h₂.desc t₁) ≫ h₁.desc t₂ := by
              rw [Category.assoc]
        _ = t₁.ι.app j ≫ h₁.desc t₂ := by rw [h₂.fac]
        _ = t₂.ι.app j := h₁.fac t₂ j
        _ = t₂.ι.app j ≫ 𝟙 _ := by simp }

@[simp]
theorem isoOfIsColimit_hom_fac
    {t₁ t₂ : Cocone F} (h₁ : IsColimit t₁) (h₂ : IsColimit t₂) (j : J) :
    t₁.ι.app j ≫ (isoOfIsColimit h₁ h₂).hom = t₂.ι.app j :=
  h₁.fac t₂ j

@[simp]
theorem isoOfIsColimit_inv_fac
    {t₁ t₂ : Cocone F} (h₁ : IsColimit t₁) (h₂ : IsColimit t₂) (j : J) :
    t₂.ι.app j ≫ (isoOfIsColimit h₁ h₂).inv = t₁.ι.app j :=
  h₂.fac t₁ j

/-- Maps out of a colimit presentation are equal when they agree on all stage
injections. -/
theorem hom_eq_of_fac
    {t : Cocone F} (h : IsColimit t) {X : C}
    (f g : t.pt ⟶ X)
    (w : ∀ j : J, t.ι.app j ≫ f = t.ι.app j ≫ g) :
    f = g := by
  exact h.hom_ext w

end InfoGeometry.Categorical.ColimitComparison
