import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import InfoGeometry.Categorical.FibonacciFusionCategoryData

/-!
# Fibonacci Hom-Spaces (Sandbox)

This file defines the explicit categorical Hom-spaces for the skeletal Fibonacci 
fusion category. Following Socratic extraction, we model morphisms between formal 
direct sums of simple objects (`FibSimple →₀ ℕ`) as pairs of complex matrices.

By Schur's Lemma, there are no non-zero morphisms between distinct simple objects, 
so a morphism `X ⟶ Y` is simply a block-diagonal matrix:
- A `X(unit) × Y(unit)` complex matrix.
- A `X(tau) × Y(tau)` complex matrix.
-/

namespace FibonacciHomSpace

open CategoryTheory
open InfoGeometry.Categorical.FibonacciFusionCategoryData

-- The objects are formal multiplicities of `𝟙` and `τ`.
abbrev FibCat := FibSimple →₀ ℕ

/-- 
The Hom-space between two objects `X` and `Y`.
It is a pair of complex matrices for the `unit` and `tau` components respectively.
-/
@[ext]
structure FibHom (X Y : FibCat) where
  unit_comp : Matrix (Fin (X FibSimple.unit)) (Fin (Y FibSimple.unit)) ℂ
  tau_comp  : Matrix (Fin (X FibSimple.tau)) (Fin (Y FibSimple.tau)) ℂ

/-- Identity morphism is the pair of identity matrices. -/
noncomputable def FibHom.id (X : FibCat) : FibHom X X :=
  { unit_comp := 1,
    tau_comp  := 1 }

/-- Composition of morphisms is matrix multiplication. -/
noncomputable def FibHom.comp {X Y Z : FibCat} (f : FibHom X Y) (g : FibHom Y Z) : FibHom X Z :=
  { unit_comp := f.unit_comp * g.unit_comp,
    tau_comp  := f.tau_comp * g.tau_comp }

/-- 
Open Debt: 
The Category instance mapping the explicit matrix operations to mathlib's `Category`.
This establishes the explicit `Hom(X, Y)` vector spaces for the Fibonacci Braided Category.
-/
noncomputable instance : Category FibCat where
  Hom X Y := FibHom X Y
  id X := FibHom.id X
  comp f g := FibHom.comp f g
  id_comp := by
    intros X Y f
    ext : 1
    · exact Matrix.one_mul f.unit_comp
    · exact Matrix.one_mul f.tau_comp
  comp_id := by
    intros X Y f
    ext : 1
    · exact Matrix.mul_one f.unit_comp
    · exact Matrix.mul_one f.tau_comp
  assoc := by
    intros W X Y Z f g h
    ext : 1
    · exact Matrix.mul_assoc f.unit_comp g.unit_comp h.unit_comp
    · exact Matrix.mul_assoc f.tau_comp g.tau_comp h.tau_comp

end FibonacciHomSpace
