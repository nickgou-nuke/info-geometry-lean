/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Two-sided crossings in a braided monoidal category

The positive and negative crossings here are the two directions of the same
braiding isomorphism.  This is deliberately an abstract categorical owner:
it does not introduce a second braid monoid, a topological fibration, or a
physical time-reversal operation.
-/

namespace InfoGeometry.Categorical.ChiralBraidDouble

open CategoryTheory
open CategoryTheory.MonoidalCategory

section Braided

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

def positiveCrossing (X Y : C) : X ⊗ Y ⟶ Y ⊗ X :=
  (β_ X Y).hom

def negativeCrossing (X Y : C) : Y ⊗ X ⟶ X ⊗ Y :=
  (β_ X Y).inv

@[simp] theorem positiveCrossing_comp_negativeCrossing (X Y : C) :
    positiveCrossing X Y ≫ negativeCrossing X Y = 𝟙 (X ⊗ Y) := by
  exact (β_ X Y).hom_inv_id

@[simp] theorem negativeCrossing_comp_positiveCrossing (X Y : C) :
    negativeCrossing X Y ≫ positiveCrossing X Y = 𝟙 (Y ⊗ X) := by
  exact (β_ X Y).inv_hom_id

/-! ## Double-braiding monodromy and balanced braided monoidal categories -/

/-- Double-braiding monodromy `M_{X,Y} = c_{X,Y} ≫ c_{Y,X} : X ⊗ Y ⟶ X ⊗ Y`
in a braided monoidal category. -/
def doubleBraidingMonodromy (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  positiveCrossing X Y ≫ positiveCrossing Y X

/-- Inverse double-braiding monodromy `M_{X,Y}⁻¹ = c_{Y,X}⁻¹ ≫ c_{X,Y}⁻¹ : X ⊗ Y ⟶ X ⊗ Y`. -/
def doubleBraidingMonodromyInv (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  negativeCrossing Y X ≫ negativeCrossing X Y

@[simp] theorem doubleBraidingMonodromy_comp_inv (X Y : C) :
    doubleBraidingMonodromy X Y ≫ doubleBraidingMonodromyInv X Y = 𝟙 (X ⊗ Y) := by
  dsimp [doubleBraidingMonodromy, doubleBraidingMonodromyInv]
  rw [Category.assoc, ← Category.assoc (positiveCrossing Y X),
    positiveCrossing_comp_negativeCrossing Y X, Category.id_comp,
    positiveCrossing_comp_negativeCrossing X Y]

@[simp] theorem doubleBraidingMonodromyInv_comp (X Y : C) :
    doubleBraidingMonodromyInv X Y ≫ doubleBraidingMonodromy X Y = 𝟙 (X ⊗ Y) := by
  dsimp [doubleBraidingMonodromy, doubleBraidingMonodromyInv]
  rw [Category.assoc, ← Category.assoc (negativeCrossing X Y),
    negativeCrossing_comp_positiveCrossing X Y, Category.id_comp,
    negativeCrossing_comp_positiveCrossing Y X]

/-- The double-braiding monodromy packaged as a categorical isomorphism `X ⊗ Y ≅ X ⊗ Y`. -/
@[simps] def doubleBraidingMonodromyIso (X Y : C) : X ⊗ Y ≅ X ⊗ Y where
  hom := doubleBraidingMonodromy X Y
  inv := doubleBraidingMonodromyInv X Y
  hom_inv_id := doubleBraidingMonodromy_comp_inv X Y
  inv_hom_id := doubleBraidingMonodromyInv_comp X Y

/-- Naturality of the double-braiding monodromy in both tensor factors. -/
theorem doubleBraidingMonodromy_naturality
    {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ doubleBraidingMonodromy X₂ Y₂ =
      doubleBraidingMonodromy X₁ Y₁ ≫ (f ⊗ₘ g) := by
  dsimp [doubleBraidingMonodromy, positiveCrossing]
  rw [← Category.assoc, BraidedCategory.braiding_naturality,
    Category.assoc, BraidedCategory.braiding_naturality, Category.assoc]

/-- In a symmetric monoidal category, the double-braiding monodromy is the identity. -/
@[simp] theorem doubleBraidingMonodromy_eq_id_of_symmetric
    {D : Type*} [Category D] [MonoidalCategory D] [SymmetricCategory D] (X Y : D) :
    doubleBraidingMonodromy X Y = 𝟙 (X ⊗ Y) :=
  SymmetricCategory.symmetry X Y

/-- The **Joyal–Street balancing coherence predicate** for a family of twist automorphisms
`twist : ∀ X : C, X ≅ X` in a braided monoidal category `C`:
- naturality `f ≫ (twist Y).hom = (twist X).hom ≫ f`,
- unit normalization `(twist (𝟙_ C)).hom = 𝟙 (𝟙_ C)`, and
- balancing coherence `(twist (X ⊗ Y)).hom = ((twist X).hom ⊗ₘ (twist Y).hom) ≫ doubleBraidingMonodromy X Y`. -/
def IsBalancedTwist (twist : ∀ X : C, X ≅ X) : Prop :=
  (∀ {X Y : C} (f : X ⟶ Y), f ≫ (twist Y).hom = (twist X).hom ≫ f) ∧
  (twist (𝟙_ C)).hom = 𝟙 (𝟙_ C) ∧
  (∀ (X Y : C),
    (twist (X ⊗ Y)).hom =
      ((twist X).hom ⊗ₘ (twist Y).hom) ≫ doubleBraidingMonodromy X Y)

namespace BalancedCategory

/-- For any Joyal–Street balanced twist family `twist : ∀ X : C, X ≅ X`, composing the inverse
factor twists `(θ_X⁻¹ ⊗ θ_Y⁻¹)` with the composite twist `θ_{X ⊗ Y}` recovers the
double-braiding monodromy `M_{X,Y} = c_{X,Y} ≫ c_{Y,X}`. -/
theorem inv_tensor_twist_comp_twist_eq_doubleBraidingMonodromy
    {twist : ∀ X : C, X ≅ X} (hBal : IsBalancedTwist twist) (X Y : C) :
    ((twist X).inv ⊗ₘ (twist Y).inv) ≫ (twist (X ⊗ Y)).hom =
      doubleBraidingMonodromy X Y := by
  simp [hBal.2.2 X Y]

/-- In any symmetric monoidal category, the identity twist family `fun X => Iso.refl X`
satisfies the Joyal–Street balancing coherence predicate `IsBalancedTwist`. -/
theorem isBalancedTwist_refl_of_symmetric
    {D : Type*} [Category D] [MonoidalCategory D] [SymmetricCategory D] :
    IsBalancedTwist (fun X : D => Iso.refl X) := by
  refine ⟨fun f => by simp, rfl, fun X Y => ?_⟩
  simp [doubleBraidingMonodromy_eq_id_of_symmetric]

end BalancedCategory

end Braided

end InfoGeometry.Categorical.ChiralBraidDouble
