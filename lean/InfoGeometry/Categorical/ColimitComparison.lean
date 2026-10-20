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

/-! ### Coherence of the canonical comparisons -/

/-- The canonical comparison is the identity when both presentations are the
    same colimit cocone. -/
theorem isoOfIsColimit_self_hom
    {t : Cocone F} (h : IsColimit t) :
    (isoOfIsColimit h h).hom = 𝟙 t.pt := by
  apply h.hom_ext
  intro j
  simp [isoOfIsColimit]

/-- Canonical comparisons compose without path dependence. -/
theorem isoOfIsColimit_hom_trans
    {t₁ t₂ t₃ : Cocone F}
    (h₁ : IsColimit t₁) (h₂ : IsColimit t₂) (h₃ : IsColimit t₃) :
    (isoOfIsColimit h₁ h₂).hom ≫ (isoOfIsColimit h₂ h₃).hom =
      (isoOfIsColimit h₁ h₃).hom := by
  apply h₁.hom_ext
  intro j
  calc
    t₁.ι.app j ≫ (isoOfIsColimit h₁ h₂).hom ≫
        (isoOfIsColimit h₂ h₃).hom =
        (t₁.ι.app j ≫ (isoOfIsColimit h₁ h₂).hom) ≫
          (isoOfIsColimit h₂ h₃).hom := by rw [Category.assoc]
    _ = t₂.ι.app j ≫ (isoOfIsColimit h₂ h₃).hom := by
      rw [isoOfIsColimit_hom_fac]
    _ = t₃.ι.app j := isoOfIsColimit_hom_fac h₂ h₃ j
    _ = t₁.ι.app j ≫ (isoOfIsColimit h₁ h₃).hom :=
      (isoOfIsColimit_hom_fac h₁ h₃ j).symm

/-- The inverse comparisons satisfy the corresponding contravariant
    composition law. -/
theorem isoOfIsColimit_inv_trans
    {t₁ t₂ t₃ : Cocone F}
    (h₁ : IsColimit t₁) (h₂ : IsColimit t₂) (h₃ : IsColimit t₃) :
    (isoOfIsColimit h₂ h₃).inv ≫ (isoOfIsColimit h₁ h₂).inv =
      (isoOfIsColimit h₁ h₃).inv := by
  apply h₃.hom_ext
  intro j
  calc
    t₃.ι.app j ≫ (isoOfIsColimit h₂ h₃).inv ≫
        (isoOfIsColimit h₁ h₂).inv =
        (t₃.ι.app j ≫ (isoOfIsColimit h₂ h₃).inv) ≫
          (isoOfIsColimit h₁ h₂).inv := by rw [Category.assoc]
    _ = t₂.ι.app j ≫ (isoOfIsColimit h₁ h₂).inv := by
      rw [isoOfIsColimit_inv_fac]
    _ = t₁.ι.app j := isoOfIsColimit_inv_fac h₁ h₂ j
    _ = t₃.ι.app j ≫ (isoOfIsColimit h₁ h₃).inv :=
      (isoOfIsColimit_inv_fac h₁ h₃ j).symm

/-! ### Transport of stagewise endomorphisms -/

/-- The cocone obtained by applying a natural endomorphism to the legs of a
    cocone. -/
def coconeMap (η : F ⟶ F) (t : Cocone F) : Cocone F where
  pt := t.pt
  ι :=
    { app := fun j => η.app j ≫ t.ι.app j
      naturality := by
        intro i j f
        calc
          F.map f ≫ η.app j ≫ t.ι.app j =
              (F.map f ≫ η.app j) ≫ t.ι.app j := by
                rw [Category.assoc]
          _ = (η.app i ≫ F.map f) ≫ t.ι.app j := by
                rw [η.naturality]
          _ = η.app i ≫ (F.map f ≫ t.ι.app j) := by
                rw [Category.assoc]
          _ = η.app i ≫ (t.ι.app i ≫ ((Functor.const J).obj t.pt).map f) := by
                rw [t.ι.naturality]
          _ = (η.app i ≫ t.ι.app i) ≫ ((Functor.const J).obj t.pt).map f := by
                rw [Category.assoc] }

/-- The endomorphism of a colimit presentation induced by a natural
    endomorphism of the underlying diagram. -/
noncomputable def colimitEnd
    (η : F ⟶ F) {t : Cocone F} (h : IsColimit t) : t.pt ⟶ t.pt :=
  h.desc (coconeMap η t)

@[simp]
theorem colimitEnd_fac
    (η : F ⟶ F) {t : Cocone F} (h : IsColimit t) (j : J) :
    t.ι.app j ≫ colimitEnd η h = η.app j ≫ t.ι.app j :=
  h.fac (coconeMap η t) j

/- Composition of natural stage endomorphisms is preserved by colimit descent. -/
theorem colimitEnd_comp
    (η μ : F ⟶ F) {t : Cocone F} (h : IsColimit t) :
    colimitEnd η h ≫ colimitEnd μ h = colimitEnd (η ≫ μ) h := by
  apply h.hom_ext
  intro j
  calc
    t.ι.app j ≫ colimitEnd η h ≫ colimitEnd μ h =
        (t.ι.app j ≫ colimitEnd η h) ≫ colimitEnd μ h := by
          rw [Category.assoc]
    _ = (η.app j ≫ t.ι.app j) ≫ colimitEnd μ h := by
          rw [colimitEnd_fac]
    _ = η.app j ≫ (t.ι.app j ≫ colimitEnd μ h) := by
          rw [Category.assoc]
    _ = η.app j ≫ (μ.app j ≫ t.ι.app j) := by
          rw [colimitEnd_fac]
    _ = (η.app j ≫ μ.app j) ≫ t.ι.app j := by
          rw [Category.assoc]
    _ = (η ≫ μ).app j ≫ t.ι.app j := by
          rfl
    _ = t.ι.app j ≫ colimitEnd (η ≫ μ) h := by
          rw [colimitEnd_fac]

/-- Canonical colimit comparisons intertwine the endomorphisms induced by a
    single natural endomorphism of the stage diagram. -/
theorem isoOfIsColimit_hom_intertwines
    (η : F ⟶ F)
    {t₁ t₂ : Cocone F} (h₁ : IsColimit t₁) (h₂ : IsColimit t₂) :
    (isoOfIsColimit h₁ h₂).hom ≫ colimitEnd η h₂ =
      colimitEnd η h₁ ≫ (isoOfIsColimit h₁ h₂).hom := by
  apply h₁.hom_ext
  intro j
  calc
    t₁.ι.app j ≫ (isoOfIsColimit h₁ h₂).hom ≫ colimitEnd η h₂ =
        (t₁.ι.app j ≫ (isoOfIsColimit h₁ h₂).hom) ≫ colimitEnd η h₂ := by
          simp only [Category.assoc]
    _ = t₂.ι.app j ≫ colimitEnd η h₂ := by
          rw [isoOfIsColimit_hom_fac]
    _ = η.app j ≫ t₂.ι.app j := colimitEnd_fac η h₂ j
    _ = η.app j ≫ (t₁.ι.app j ≫ (isoOfIsColimit h₁ h₂).hom) := by
          rw [isoOfIsColimit_hom_fac]
    _ = (η.app j ≫ t₁.ι.app j) ≫
          (isoOfIsColimit h₁ h₂).hom := by
          rw [Category.assoc]
    _ = (t₁.ι.app j ≫ colimitEnd η h₁) ≫
          (isoOfIsColimit h₁ h₂).hom := by
          rw [colimitEnd_fac η h₁ j]
    _ = t₁.ι.app j ≫ colimitEnd η h₁ ≫
          (isoOfIsColimit h₁ h₂).hom := by
          rw [Category.assoc]

end InfoGeometry.Categorical.ColimitComparison
