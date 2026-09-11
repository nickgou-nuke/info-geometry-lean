import InfoGeometry.Cocycle.GroupoidCocycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Logarithmic Groupoid Cocycle Calculus

This file owns the additive/logarithmic version of the groupoid chain rule.
It is the formal target for logarithms of determinant, Jacobian,
Radon-Nikodym, and modular cocycles whenever the coefficient system has an
additive logarithmic form.

The convention matches `GroupoidCocycle`: for `f : X ⟶ Y`, coefficients over
`Y` are transported back to coefficients over `X`, and

`ℓ (f ≫ g) = ℓ f + f! (ℓ g)`.
-/

noncomputable section

namespace InfoGeometry.Cocycle

open CategoryTheory

universe u v

/-- A contravariant additive coefficient system on a category/groupoid. -/
structure GroupoidAdditiveCoefficientSystem
    (Γ : Type u) [Category.{v} Γ] where
  coeff : Γ → Type v
  instAddGroup : ∀ X : Γ, AddGroup (coeff X)
  transport : ∀ {X Y : Γ}, (X ⟶ Y) → coeff Y →+ coeff X
  transport_id : ∀ X : Γ, transport (𝟙 X) = AddMonoidHom.id (coeff X)
  transport_comp :
    ∀ {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z),
      transport (f ≫ g) = (transport f).comp (transport g)

attribute [instance] GroupoidAdditiveCoefficientSystem.instAddGroup

namespace GroupoidAdditiveCoefficientSystem

variable {Γ : Type u} [Category.{v} Γ]
variable (C : GroupoidAdditiveCoefficientSystem Γ)

@[simp]
theorem transport_id_apply (X : Γ) (u : C.coeff X) :
    C.transport (𝟙 X) u = u := by
  rw [C.transport_id]
  rfl

@[simp]
theorem transport_comp_apply {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (u : C.coeff Z) :
    C.transport (f ≫ g) u = C.transport f (C.transport g u) := by
  rw [C.transport_comp]
  rfl

end GroupoidAdditiveCoefficientSystem

/--
An additive one-cocycle over a category/groupoid.

This is the logarithmic form of the multiplicative chain rule.
-/
structure GroupoidAdditiveCocycle
    {Γ : Type u} [Category.{v} Γ]
    (C : GroupoidAdditiveCoefficientSystem Γ) where
  toFun : ∀ {X Y : Γ}, (X ⟶ Y) → C.coeff X
  map_id : ∀ X : Γ, toFun (𝟙 X) = 0
  map_comp :
    ∀ {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z),
      toFun (f ≫ g) = toFun f + C.transport f (toFun g)

namespace GroupoidAdditiveCocycle

variable {Γ : Type u} [Category.{v} Γ]
variable {C : GroupoidAdditiveCoefficientSystem Γ}

@[simp]
theorem map_id_apply (c : GroupoidAdditiveCocycle C) (X : Γ) :
    c.toFun (𝟙 X) = 0 :=
  c.map_id X

theorem chain_rule (c : GroupoidAdditiveCocycle C)
    {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.toFun (f ≫ g) = c.toFun f + C.transport f (c.toFun g) :=
  c.map_comp f g

/--
The canonical additive coboundary attached to a choice of local potential `b`.

This is the logarithmic version of changing trivialization or reference density.
-/
def coboundary (b : ∀ X : Γ, C.coeff X) :
    GroupoidAdditiveCocycle C where
  toFun := fun {X Y} f => b X - C.transport f (b Y)
  map_id := by
    intro X
    rw [C.transport_id]
    simp
  map_comp := by
    intro X Y Z f g
    rw [C.transport_comp]
    simp [sub_eq_add_neg, add_assoc]

@[simp]
theorem coboundary_apply (b : ∀ X : Γ, C.coeff X)
    {X Y : Γ} (f : X ⟶ Y) :
    (coboundary (C := C) b).toFun f =
      b X - C.transport f (b Y) :=
  rfl

end GroupoidAdditiveCocycle

end InfoGeometry.Cocycle
