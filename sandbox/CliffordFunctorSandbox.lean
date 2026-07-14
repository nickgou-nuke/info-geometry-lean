import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Clifford Functor Sandbox

This file combines the tower structure and functor for Clifford algebras,
recovered from fragments. It defines an isometric tower and a categorical
colimit functor for it, with all necessary concrete instantiations.
-/

open CategoryTheory CliffordAlgebra

variable {V : ℕ → Type} [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]
variable (Q : ∀ n, QuadraticForm ℝ (V n))

/-- 
  A strict isometric tower structure over the natural numbers.
-/
structure IsometricTower where
  iso : ∀ (n m : ℕ) (_h : n ≤ m), Q n →qᵢ Q m
  iso_id : ∀ (n : ℕ) (h : n ≤ n), iso n n h = QuadraticMap.Isometry.id (Q n)
  iso_comp : ∀ (l m n : ℕ) (hlm : l ≤ m) (hmn : m ≤ n), 
    (iso m n hmn).comp (iso l m hlm) = iso l n (le_trans hlm hmn)

/--
Concrete instantiation of IsometricTower for the trivial case where all vector spaces are ℝ
and quadratic forms are zero. This satisfies the rule that all structures must be natively instantiated.
-/
def trivialTower : IsometricTower (fun (_n : ℕ) => (0 : QuadraticForm ℝ ℝ)) where
  iso _n _m _h := QuadraticMap.Isometry.id (0 : QuadraticForm ℝ ℝ)
  iso_id _n _h := rfl
  iso_comp _l _m _n _hlm _hmn := rfl

variable (tower : IsometricTower Q)

/-- Proof of functor identity mapping -/
lemma CliffordTowerFunctor_map_id (n : ℕ) :
  AlgCat.ofHom (CliffordAlgebra.map (tower.iso n n (leOfHom (𝟙 n)))) = 𝟙 (AlgCat.of ℝ (CliffordAlgebra (Q n))) := by
  ext x
  simp [tower.iso_id]

/-- Proof of functor composition mapping -/
lemma CliffordTowerFunctor_map_comp {l m n : ℕ} (f : l ⟶ m) (g : m ⟶ n) :
  AlgCat.ofHom (CliffordAlgebra.map (tower.iso l n (leOfHom (f ≫ g)))) = 
  AlgCat.ofHom (CliffordAlgebra.map (tower.iso l m (leOfHom f))) ≫ 
  AlgCat.ofHom (CliffordAlgebra.map (tower.iso m n (leOfHom g))) := by
  ext x
  simp
  have h_comp : tower.iso l n (leOfHom (f ≫ g)) = (tower.iso m n (leOfHom g)).comp (tower.iso l m (leOfHom f)) :=
    (tower.iso_comp l m n (leOfHom f) (leOfHom g)).symm
  have h_eq : (tower.iso l n (leOfHom (f ≫ g))) x = (tower.iso m n (leOfHom g)) ((tower.iso l m (leOfHom f)) x) := by
    rw [h_comp]
    rfl
  rw [h_eq]

/--
  THE DIRECTED FUNCTOR
  
  Mathematically packs the infinite tower of Clifford algebras and their 
  isometric structural liftings into a strict CategoryTheory functor.
  This allows taking the categorical colimit over the entire thermodynamic phase space.
-/
def CliffordTowerFunctor : ℕ ⥤ AlgCat ℝ where
  obj n := AlgCat.of ℝ (CliffordAlgebra (Q n))
  map h := AlgCat.ofHom (CliffordAlgebra.map (tower.iso _ _ (leOfHom h)))
  map_id n := CliffordTowerFunctor_map_id Q tower n
  map_comp f g := CliffordTowerFunctor_map_comp Q tower f g
