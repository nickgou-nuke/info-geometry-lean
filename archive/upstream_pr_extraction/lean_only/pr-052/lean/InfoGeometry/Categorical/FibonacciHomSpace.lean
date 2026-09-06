import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
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

namespace InfoGeometry.Categorical.FibonacciHomSpace

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

instance : Zero (FibHom X Y) :=
  ⟨{ unit_comp := 0, tau_comp := 0 }⟩

instance : Add (FibHom X Y) :=
  ⟨fun f g => { unit_comp := f.unit_comp + g.unit_comp, tau_comp := f.tau_comp + g.tau_comp }⟩

instance : Neg (FibHom X Y) :=
  ⟨fun f => { unit_comp := -f.unit_comp, tau_comp := -f.tau_comp }⟩

instance : SMul ℂ (FibHom X Y) :=
  ⟨fun c f => { unit_comp := c • f.unit_comp, tau_comp := c • f.tau_comp }⟩

instance : AddCommGroup (FibHom X Y) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc f g h := by
    apply FibHom.ext
    · change (f.unit_comp + g.unit_comp) + h.unit_comp = _
      exact add_assoc _ _ _
    · change (f.tau_comp + g.tau_comp) + h.tau_comp = _
      exact add_assoc _ _ _
  zero_add f := by
    apply FibHom.ext
    · change 0 + f.unit_comp = _
      exact zero_add _
    · change 0 + f.tau_comp = _
      exact zero_add _
  add_zero f := by
    apply FibHom.ext
    · change f.unit_comp + 0 = _
      exact add_zero _
    · change f.tau_comp + 0 = _
      exact add_zero _
  neg_add_cancel f := by
    apply FibHom.ext
    · change -f.unit_comp + f.unit_comp = _
      exact neg_add_cancel _
    · change -f.tau_comp + f.tau_comp = _
      exact neg_add_cancel _
  add_comm f g := by
    apply FibHom.ext
    · change f.unit_comp + g.unit_comp = _
      exact add_comm _ _
    · change f.tau_comp + g.tau_comp = _
      exact add_comm _ _

instance : Module ℂ (FibHom X Y) where
  one_smul f := by
    apply FibHom.ext
    · change (1 : ℂ) • f.unit_comp = _
      exact one_smul ℂ _
    · change (1 : ℂ) • f.tau_comp = _
      exact one_smul ℂ _
  mul_smul c d f := by
    apply FibHom.ext
    · change (c * d) • f.unit_comp = c • d • f.unit_comp
      exact mul_smul c d f.unit_comp
    · change (c * d) • f.tau_comp = c • d • f.tau_comp
      exact mul_smul c d f.tau_comp
  smul_zero c := by
    apply FibHom.ext
    · change c • (0 : Matrix (Fin (X FibSimple.unit)) (Fin (Y FibSimple.unit)) ℂ) = _
      exact smul_zero _
    · change c • (0 : Matrix (Fin (X FibSimple.tau)) (Fin (Y FibSimple.tau)) ℂ) = _
      exact smul_zero _
  smul_add c f g := by
    apply FibHom.ext
    · change c • (f.unit_comp + g.unit_comp) = _
      exact smul_add _ _ _
    · change c • (f.tau_comp + g.tau_comp) = _
      exact smul_add _ _ _
  add_smul c d f := by
    apply FibHom.ext
    · change (c + d) • f.unit_comp = _
      exact add_smul _ _ _
    · change (c + d) • f.tau_comp = _
      exact add_smul _ _ _
  zero_smul f := by
    apply FibHom.ext
    · change (0 : ℂ) • f.unit_comp = _
      exact zero_smul ℂ _
    · change (0 : ℂ) • f.tau_comp = _
      exact zero_smul ℂ _

/-- Identity morphism is the pair of identity matrices. -/
noncomputable def FibHom.id (X : FibCat) : FibHom X X :=
  { unit_comp := 1,
    tau_comp  := 1 }

/-- Composition of morphisms is matrix multiplication. -/
noncomputable def FibHom.comp {X Y Z : FibCat} (f : FibHom X Y) (g : FibHom Y Z) : FibHom X Z :=
  { unit_comp := f.unit_comp * g.unit_comp,
    tau_comp  := f.tau_comp * g.tau_comp }

theorem FibHom.comp_add_left {X Y Z : FibCat}
    (f g : FibHom X Y) (h : FibHom Y Z) :
    FibHom.comp (f + g) h = FibHom.comp f h + FibHom.comp g h := by
  apply FibHom.ext
  · exact Matrix.add_mul _ _ _
  · exact Matrix.add_mul _ _ _

theorem FibHom.comp_add_right {X Y Z : FibCat}
    (f : FibHom X Y) (g h : FibHom Y Z) :
    FibHom.comp f (g + h) = FibHom.comp f g + FibHom.comp f h := by
  apply FibHom.ext
  · exact Matrix.mul_add _ _ _
  · exact Matrix.mul_add _ _ _

theorem FibHom.comp_zero_left {X Y Z : FibCat}
    (f : FibHom Y Z) :
    FibHom.comp (0 : FibHom X Y) f = 0 := by
  apply FibHom.ext
  · change (0 : Matrix (Fin (X FibSimple.unit)) (Fin (Y FibSimple.unit)) ℂ) *
      f.unit_comp = 0
    exact Matrix.zero_mul _
  · change (0 : Matrix (Fin (X FibSimple.tau)) (Fin (Y FibSimple.tau)) ℂ) *
      f.tau_comp = 0
    exact Matrix.zero_mul _

theorem FibHom.comp_zero_right {X Y Z : FibCat}
    (f : FibHom X Y) :
    FibHom.comp f (0 : FibHom Y Z) = 0 := by
  apply FibHom.ext
  · change f.unit_comp *
      (0 : Matrix (Fin (Y FibSimple.unit)) (Fin (Z FibSimple.unit)) ℂ) = 0
    exact Matrix.mul_zero _
  · change f.tau_comp *
      (0 : Matrix (Fin (Y FibSimple.tau)) (Fin (Z FibSimple.tau)) ℂ) = 0
    exact Matrix.mul_zero _

theorem FibHom.comp_smul_left {X Y Z : FibCat}
    (c : ℂ) (f : FibHom X Y) (g : FibHom Y Z) :
    FibHom.comp (c • f) g = c • FibHom.comp f g := by
  apply FibHom.ext
  · exact Matrix.smul_mul _ _ _
  · exact Matrix.smul_mul _ _ _

theorem FibHom.comp_smul_right {X Y Z : FibCat}
    (c : ℂ) (f : FibHom X Y) (g : FibHom Y Z) :
    FibHom.comp f (c • g) = c • FibHom.comp f g := by
  apply FibHom.ext
  · exact Matrix.mul_smul f.unit_comp c g.unit_comp
  · exact Matrix.mul_smul f.tau_comp c g.tau_comp

/-- 
The explicit matrix operations are already packaged as a native `Category`
instance below, with `Hom(X, Y) = FibHom X Y`.  The remaining boundary is
not the category instance itself: a full bundled monoidal/braided promotion
still requires the corresponding naturality and coherence fields.
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

noncomputable instance : Preadditive FibCat where
  homGroup := fun P Q => by
    change AddCommGroup (FibHom P Q)
    infer_instance
  add_comp := by
    intro X Y Z f g h
    exact FibHom.comp_add_left f g h
  comp_add := by
    intro X Y Z f g h
    exact FibHom.comp_add_right f g h

end InfoGeometry.Categorical.FibonacciHomSpace
