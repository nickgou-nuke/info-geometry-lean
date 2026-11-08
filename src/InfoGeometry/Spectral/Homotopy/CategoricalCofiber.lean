import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Categorical cofiber boundary

The original Spectral development uses a higher inductive pushout.  This file
records the honest ordinary categorical analogue in `Type`: the pushout of a
map with the unique map to `Unit`.  It is intentionally separate from the
finite pointed readout, so no 1-categorical construction is confused with a
HoTT cofiber.
-/

namespace InfoGeometry.Spectral.Homotopy.CategoricalCofiber

open CategoryTheory CategoryTheory.Limits

variable {α β γ : Type}

private def pointMap (α : Type) : α ⟶ Unit := TypeCat.ofHom fun _ => ()

noncomputable def carrier (f : α → β) : Type :=
  pushout (TypeCat.ofHom f) (pointMap α)

noncomputable def quotient (f : α → β) : β → carrier f :=
  pushout.inl (TypeCat.ofHom f) (pointMap α)

noncomputable def basepoint (f : α → β) : Unit → carrier f :=
  pushout.inr (TypeCat.ofHom f) (pointMap α)

@[simp]
theorem quotient_glue (f : α → β) (x : α) :
    quotient f (f x) = basepoint f () := by
  exact ConcreteCategory.congr_hom
    (pushout.condition (f := TypeCat.ofHom f) (g := pointMap α)) x

noncomputable def lift
    (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) : carrier f → γ :=
  pushout.desc (f := TypeCat.ofHom f) (g := pointMap α)
    (TypeCat.ofHom u) (TypeCat.ofHom v) (by
    apply ConcreteCategory.ext_apply
    intro x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk] using h x)

@[simp]
theorem lift_quotient
    (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) (y : β) :
    lift f u v h (quotient f y) = u y := by
  exact ConcreteCategory.congr_hom (pushout.inl_desc
    (f := TypeCat.ofHom f) (g := pointMap α)
    (TypeCat.ofHom u) (TypeCat.ofHom v) (by
      apply ConcreteCategory.ext_apply
      intro x
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk] using h x)) y

@[simp]
theorem lift_basepoint
    (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) :
    lift f u v h (basepoint f ()) = v () := by
  exact ConcreteCategory.congr_hom (pushout.inr_desc
    (f := TypeCat.ofHom f) (g := pointMap α)
    (TypeCat.ofHom u) (TypeCat.ofHom v) (by
      apply ConcreteCategory.ext_apply
      intro x
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk] using h x)) ()

theorem lift_unique
    (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ())
    (k : carrier f → γ)
    (hk : ∀ y, k (quotient f y) = u y)
    (hk' : k (basepoint f ()) = v ()) :
    k = lift f u v h := by
  funext z
  have hk₁ :
      pushout.inl (TypeCat.ofHom f) (pointMap α) ≫ TypeCat.ofHom k =
        pushout.inl (TypeCat.ofHom f) (pointMap α) ≫ TypeCat.ofHom (lift f u v h) := by
    ext y
    change k (quotient f y) = lift f u v h (quotient f y)
    rw [hk y, lift_quotient]
  have hk₂ :
      pushout.inr (TypeCat.ofHom f) (pointMap α) ≫ TypeCat.ofHom k =
        pushout.inr (TypeCat.ofHom f) (pointMap α) ≫ TypeCat.ofHom (lift f u v h) := by
    ext p
    cases p
    change k (basepoint f ()) = lift f u v h (basepoint f ())
    rw [hk', lift_basepoint]
  exact ConcreteCategory.congr_hom (pushout.hom_ext hk₁ hk₂) z

end InfoGeometry.Spectral.Homotopy.CategoricalCofiber
