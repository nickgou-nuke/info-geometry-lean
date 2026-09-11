import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import InfoGeometry.Sandbox.CliffordFunctorSandbox.Tower

/-!
# Directed Graph Functor for Clifford Towers

This file packs the lifted algebra homomorphisms into a strict 
directed graph category functor over the natural numbers ℕ.
-/

open CategoryTheory CliffordAlgebra

variable {V : ℕ → Type} [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]
variable (Q : ∀ n, QuadraticForm ℝ (V n))
variable (tower : IsometricTower Q)

/--
  THE DIRECTED FUNCTOR
  
  Mathematically packs the infinite tower of Clifford algebras and their 
  isometric structural liftings into a strict CategoryTheory functor.
  This allows taking the categorical colimit over the entire thermodynamic phase space.
-/
def CliffordTowerFunctor : ℕ ⥤ AlgCat ℝ where
  obj n := AlgCat.of ℝ (CliffordAlgebra (Q n))
  map {n m} h := AlgCat.ofHom (CliffordAlgebra.map (tower.iso n m (leOfHom h)))
  map_id X := by
    ext x
    simp [tower.iso_id]
  map_comp {l m n} f g := by
    ext x
    simp
    have h_comp : tower.iso l n (leOfHom (f ≫ g)) = (tower.iso m n (leOfHom g)).comp (tower.iso l m (leOfHom f)) :=
      (tower.iso_comp l m n (leOfHom f) (leOfHom g)).symm
    have h_eq : (tower.iso l n (leOfHom (f ≫ g))) x = (tower.iso m n (leOfHom g)) ((tower.iso l m (leOfHom f)) x) := by
      rw [h_comp]
      rfl
    rw [h_eq]
