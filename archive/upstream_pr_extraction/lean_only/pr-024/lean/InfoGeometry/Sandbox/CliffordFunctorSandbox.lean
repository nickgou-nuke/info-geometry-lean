import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Real.Basic

/-!
# Sandbox: Directed Graph Functor for Clifford Towers

This file packs the lifted algebra homomorphisms into a strict 
directed graph category functor over the natural numbers ℕ.
-/

open CategoryTheory CliffordAlgebra

variable {V : ℕ → Type} [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]
variable (Q : ∀ n, QuadraticForm ℝ (V n))

-- Assume we have an isometric embedding for every inequality n ≤ m in the poset ℕ
variable (iso : ∀ (n m : ℕ) (h : n ≤ m), Q n →qᵢ Q m)
variable (iso_comp : ∀ (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n), 
  (iso m n hmn).comp (iso l m hlm) = iso l n (le_trans hlm hmn))

/--
  THE DIRECTED FUNCTOR
  
  Mathematically packs the infinite tower of Clifford algebras and their 
  isometric structural liftings into a strict CategoryTheory functor.
  This allows taking the categorical colimit over the entire thermodynamic phase space.
-/
def CliffordTowerFunctor : ℕ ⥤ AlgCat ℝ where
  obj n := AlgCat.of ℝ (CliffordAlgebra (Q n))
  map {n m} h := AlgCat.ofHom (CliffordAlgebra.map (iso n m (leOfHom h)))
  map_id X := by ext; rfl
  map_comp {l m n} f g := by
    ext x
    dsimp
    have h_comp : (iso m n (leOfHom g)).comp (iso l m (leOfHom f)) = iso l n (leOfHom (f ≫ g)) := by
      -- leOfHom (f ≫ g) is le_trans (leOfHom f) (leOfHom g)
      exact iso_comp l m n (leOfHom f) (leOfHom g)
    rw [← h_comp, CliffordAlgebra.map_comp_map]
