import Mathlib.CategoryTheory.Groupoid
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Tactic

/-!
# Groupoid Cocycle Calculus

This file owns the abstract chain-rule skeleton used by determinant,
Jacobian, Radon-Nikodym, and Connes-type cocycles.

The multiplicative convention is contravariant in the arrow:
for `f : X ⟶ Y`, coefficients over `Y` are transported back to
coefficients over `X`. A cocycle therefore satisfies

`c (f ≫ g) = c f * f! (c g)`.

Current-algebra anomalies are deliberately not encoded here; those are
central two-cocycles and live in the Wick/current algebra layer.
-/

noncomputable section

namespace InfoGeometry.Cocycle

open CategoryTheory

universe u v

/-- A contravariant multiplicative coefficient system on a category/groupoid. -/
structure GroupoidMultiplicativeCoefficientSystem
    (Γ : Type u) [Category.{v} Γ] where
  coeff : Γ → Type v
  instGroup : ∀ X : Γ, Group (coeff X)
  transport : ∀ {X Y : Γ}, (X ⟶ Y) → coeff Y →* coeff X
  transport_id : ∀ X : Γ, transport (𝟙 X) = MonoidHom.id (coeff X)
  transport_comp :
    ∀ {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z),
      transport (f ≫ g) = (transport f).comp (transport g)

attribute [instance] GroupoidMultiplicativeCoefficientSystem.instGroup

namespace GroupoidMultiplicativeCoefficientSystem

variable {Γ : Type u} [Category.{v} Γ]
variable (C : GroupoidMultiplicativeCoefficientSystem Γ)

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

end GroupoidMultiplicativeCoefficientSystem

/--
A multiplicative one-cocycle over a category/groupoid.

For a transformation `f : X ⟶ Y`, the value `toFun f` lies in the coefficient
group over the source `X`, and composition obeys the functorial chain rule.
-/
structure GroupoidMultiplicativeCocycle
    {Γ : Type u} [Category.{v} Γ]
    (C : GroupoidMultiplicativeCoefficientSystem Γ) where
  toFun : ∀ {X Y : Γ}, (X ⟶ Y) → C.coeff X
  map_id : ∀ X : Γ, toFun (𝟙 X) = 1
  map_comp :
    ∀ {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z),
      toFun (f ≫ g) = toFun f * C.transport f (toFun g)

namespace GroupoidMultiplicativeCocycle

variable {Γ : Type u} [Category.{v} Γ]
variable {C : GroupoidMultiplicativeCoefficientSystem Γ}

@[simp]
theorem map_id_apply (c : GroupoidMultiplicativeCocycle C) (X : Γ) :
    c.toFun (𝟙 X) = 1 :=
  c.map_id X

theorem chain_rule (c : GroupoidMultiplicativeCocycle C)
    {X Y Z : Γ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.toFun (f ≫ g) = c.toFun f * C.transport f (c.toFun g) :=
  c.map_comp f g

/--
The canonical multiplicative coboundary attached to a choice of local
trivialization `b`.

It is included here because it is the formal version of changing density,
gauge, normalization, or reference state.
-/
def coboundary (b : ∀ X : Γ, C.coeff X) :
    GroupoidMultiplicativeCocycle C where
  toFun := fun {X Y} f => b X * (C.transport f (b Y))⁻¹
  map_id := by
    intro X
    rw [C.transport_id]
    simp
  map_comp := by
    intro X Y Z f g
    rw [C.transport_comp]
    simp [mul_assoc]

@[simp]
theorem coboundary_apply (b : ∀ X : Γ, C.coeff X)
    {X Y : Γ} (f : X ⟶ Y) :
    (coboundary (C := C) b).toFun f =
      b X * (C.transport f (b Y))⁻¹ :=
  rfl

end GroupoidMultiplicativeCocycle

/-! ## Constant-coefficient category/groupoid cocycles -/

section CategoryCocycles

variable {Γ U : Type*} [Category Γ] [Monoid U]

/--
A multiplicative cocycle on a category with constant coefficient monoid is a
functor into the one-object category `SingleObj U`.

For groupoids this is the constant-coefficient specialization of the
groupoid cocycle calculus.
-/
abbrev CategoryMultiplicativeCocycle (Γ U : Type*) [Category Γ] [Monoid U] :=
  Γ ⥤ SingleObj U

/--
The category/groupoid multiplicative chain rule.

Mathlib's one-object category convention is
`f ≫ g = g * f`, so for `γ : X ⟶ Y` and `η : Y ⟶ Z` the functorial
chain rule reads `c (γ ≫ η) = c η * c γ`.
-/
theorem categoryMultiplicativeCocycle_chain_rule
    (C : CategoryMultiplicativeCocycle Γ U) {X Y Z : Γ}
    (γ : X ⟶ Y) (η : Y ⟶ Z) :
    C.map (γ ≫ η) = C.map η * C.map γ := by
  simp [SingleObj.comp_as_mul]

@[simp]
theorem categoryMultiplicativeCocycle_id
    (C : CategoryMultiplicativeCocycle Γ U) (X : Γ) :
    C.map (𝟙 X) = 1 := by
  simp [SingleObj.id_as_one]

end CategoryCocycles

section GroupoidCocycles

variable {Γ U : Type*} [Groupoid Γ] [Group U]

/--
On a groupoid, the cocycle value of the inverse morphism is a left inverse of
the cocycle value of the morphism.
-/
theorem groupoidMultiplicativeCocycle_inv_mul
    (C : CategoryMultiplicativeCocycle Γ U) {X Y : Γ} (γ : X ⟶ Y) :
    C.map (CategoryTheory.inv γ) * C.map γ = 1 := by
  rw [Functor.map_inv, SingleObj.inv_as_inv]
  exact inv_mul_cancel (C.map γ)

/--
On a groupoid, the cocycle value of the inverse morphism is also a right
inverse of the cocycle value of the morphism.
-/
theorem groupoidMultiplicativeCocycle_mul_inv
    (C : CategoryMultiplicativeCocycle Γ U) {X Y : Γ} (γ : X ⟶ Y) :
    C.map γ * C.map (CategoryTheory.inv γ) = 1 := by
  rw [Functor.map_inv, SingleObj.inv_as_inv]
  exact mul_inv_cancel (C.map γ)

end GroupoidCocycles

end InfoGeometry.Cocycle
