import InfoGeometry.Spectral.Algebra.ChainComplex

/-!
# Morphisms of module chain complexes

This small adapter exposes the native component and commuting-square fields
of Mathlib homological-complex morphisms under the vocabulary used by the
Spectral port.
-/

namespace InfoGeometry.Spectral.Algebra.ModuleChainComplex

open CategoryTheory

universe u

variable {R : Type u} [Ring R]

abbrev Map (C D : Carrier R) := C.Hom D

variable {C D : Carrier R}

variable {E F : Carrier R}

/-- Identity and composition are inherited from the Mathlib category. -/
abbrev id (C : Carrier R) : Map C C := 𝟙 C

@[simp] theorem id_component (C : Carrier R) (n : ℕ) :
    (id C).f n = 𝟙 (C.X n) := rfl


theorem map_comm (f : Map C D) (i j : ℕ)
    (h : (ComplexShape.down ℕ).Rel i j) :
    f.f i ≫ D.d i j = C.d i j ≫ f.f j :=
  f.comm' i j h

theorem map_ext {f g : Map C D} (h : ∀ n, f.f n = g.f n) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact h n

/- Composition is the componentwise composition of chain maps.  Keeping it
explicit avoids depending on a categorical instance for the adapter alias. -/
def comp (g : Map D E) (f : Map C D) : Map C E where
  f n := f.f n ≫ g.f n
  comm' i j h := by
    rw [Category.assoc, g.comm' i j h, ← Category.assoc, f.comm' i j h]
    simp only [Category.assoc]

@[simp] theorem comp_component (g : Map D E) (f : Map C D) (n : ℕ) :
    (comp g f).f n = f.f n ≫ g.f n :=
  rfl

@[simp] theorem comp_id (f : Map C D) :
    comp (id D) f = f := by
  apply map_ext
  intro n
  simp [comp]

@[simp] theorem id_comp (f : Map C D) :
    comp f (id C) = f := by
  apply map_ext
  intro n
  simp [comp]

theorem comp_assoc (h : Map E F) (g : Map D E) (f : Map C D) :
    comp h (comp g f) = comp (comp h g) f := by
  apply map_ext
  intro n
  simp [comp, Category.assoc]

end InfoGeometry.Spectral.Algebra.ModuleChainComplex
