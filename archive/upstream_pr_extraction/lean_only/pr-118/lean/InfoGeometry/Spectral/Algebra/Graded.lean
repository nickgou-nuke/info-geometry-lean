import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Graded module families

The old Spectral reference uses graded modules and maps whose degree is an
endofunction on the grading type. This file ports the reusable categorical
core without reproducing the old dependent path-transport implementation.
-/

namespace InfoGeometry.Spectral.Algebra

open CategoryTheory

universe u v

/-- A graded module family, represented in the native `ModuleCat` carrier. -/
abbrev GradedModule (R : Type u) (I : Type v) [Ring R] := I → ModuleCat R

namespace GradedModule

variable {R : Type u} {I : Type v} [Ring R]

/-- A homogeneous map with an explicitly recorded degree function. -/
structure Hom (M N : GradedModule R I) where
  degree : I → I
  map : ∀ i, M i ⟶ N (degree i)

namespace Hom

variable {M N P : GradedModule R I}

def app (f : Hom M N) (i : I) : M i ⟶ N (f.degree i) := f.map i

@[simp] theorem app_eq_map (f : Hom M N) (i : I) : f.app i = f.map i := rfl

/-- Identity homogeneous map. -/
def id (M : GradedModule R I) : Hom M M where
  degree := fun i => i
  map := fun i => 𝟙 (M i)

@[simp] theorem id_degree (M : GradedModule R I) (i : I) : (id M).degree i = i := rfl

@[simp] theorem id_app (M : GradedModule R I) (i : I) :
    (id M).app i = 𝟙 (M i) := rfl

/-- Composition of homogeneous maps, with the composite degree function. -/
def comp (g : Hom N P) (f : Hom M N) : Hom M P where
  degree := fun i => g.degree (f.degree i)
  map := fun i => f.map i ≫ g.map (f.degree i)

infixr:80 " ⋙ " => comp

@[simp] theorem comp_degree (g : Hom N P) (f : Hom M N) (i : I) :
    (g ⋙ f).degree i = g.degree (f.degree i) := rfl

@[simp] theorem comp_app (g : Hom N P) (f : Hom M N) (i : I) :
    (g ⋙ f).app i = f.app i ≫ g.app (f.degree i) := rfl

end Hom
end GradedModule
end InfoGeometry.Spectral.Algebra
