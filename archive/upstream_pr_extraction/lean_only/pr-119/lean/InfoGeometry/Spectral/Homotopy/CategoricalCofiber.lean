import Mathlib

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

private def pointMap (α : Type) : α ⟶ Unit := fun _ => ()

noncomputable def carrier (f : α → β) : Type :=
  pushout f (pointMap α)

noncomputable def quotient (f : α → β) : β → carrier f :=
  pushout.inl f (pointMap α)

noncomputable def basepoint (f : α → β) : Unit → carrier f :=
  pushout.inr f (pointMap α)

@[simp]
theorem quotient_glue (f : α → β) (x : α) :
    quotient f (f x) = basepoint f () := by
  exact congrFun (pushout.condition (f := f) (g := pointMap α)) x

noncomputable def lift
    (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) : carrier f → γ :=
  pushout.desc u v (by
    change (f : α ⟶ β) ≫ (u : β ⟶ γ) =
      (pointMap α : α ⟶ Unit) ≫ (v : Unit ⟶ γ)
    ext x
    exact h x)

@[simp]
theorem lift_quotient
    (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) (y : β) :
    lift f u v h (quotient f y) = u y := by
  exact congrFun (pushout.inl_desc u v (by
    change (f : α ⟶ β) ≫ (u : β ⟶ γ) =
      (pointMap α : α ⟶ Unit) ≫ (v : Unit ⟶ γ)
    ext x
    exact h x)) y

@[simp]
theorem lift_basepoint
    (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) :
    lift f u v h (basepoint f ()) = v () := by
  exact congrFun (pushout.inr_desc u v (by
    change (f : α ⟶ β) ≫ (u : β ⟶ γ) =
      (pointMap α : α ⟶ Unit) ≫ (v : Unit ⟶ γ)
    ext x
    exact h x)) ()

theorem lift_unique
    (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ())
    (k : carrier f → γ)
    (hk : ∀ y, k (quotient f y) = u y)
    (hk' : k (basepoint f ()) = v ()) :
    k = lift f u v h := by
  funext z
  have hk₁ :
      pushout.inl f (pointMap α) ≫ k =
        pushout.inl f (pointMap α) ≫ lift f u v h := by
    change (fun y => k (quotient f y)) =
      fun y => lift f u v h (quotient f y)
    funext y
    rw [hk y, lift_quotient]
  have hk₂ :
      pushout.inr f (pointMap α) ≫ k =
        pushout.inr f (pointMap α) ≫ lift f u v h := by
    change (fun p => k (basepoint f p)) =
      fun p => lift f u v h (basepoint f p)
    funext p
    cases p
    rw [hk', lift_basepoint]
  exact congrFun (pushout.hom_ext hk₁ hk₂) z

end InfoGeometry.Spectral.Homotopy.CategoricalCofiber
