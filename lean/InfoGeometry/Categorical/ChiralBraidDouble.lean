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

end InfoGeometry.Categorical.ChiralBraidDouble
