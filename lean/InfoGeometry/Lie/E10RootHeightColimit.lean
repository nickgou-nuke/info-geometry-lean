import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Quotient
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Lie.E10SerrePresentation

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CartanMatrix

namespace InfoGeometry.Lie.E10

/-!
# 1. Assign root-lattice degrees to the Serre generators
-/
abbrev RootLattice := Fin 10 → ℤ

def generatorDegree : CartanMatrix.Generators (Fin 10) → RootLattice
  | .H _ => 0
  | .E i => fun j => if j = i then 1 else 0
  | .F i => fun j => if j = i then -1 else 0

/-!
# 2. Extend degree through free-Lie brackets
-/
inductive IsHomogeneous : RootLattice → FreeLieAlgebra ℚ (Generators (Fin 10)) → Prop
  | of (x : Generators (Fin 10)) : IsHomogeneous (generatorDegree x) (FreeLieAlgebra.of ℚ x)
  | zero (a : RootLattice) : IsHomogeneous a 0
  | smul (a : RootLattice) (c : ℚ) (u : FreeLieAlgebra ℚ (Generators (Fin 10))) (hu : IsHomogeneous a u) : IsHomogeneous a (c • u)
  | add (a : RootLattice) (u v : FreeLieAlgebra ℚ (Generators (Fin 10))) (hu : IsHomogeneous a u) (hv : IsHomogeneous a v) : IsHomogeneous a (u + v)
  | bracket (a b : RootLattice) (u v : FreeLieAlgebra ℚ (Generators (Fin 10))) (hu : IsHomogeneous a u) (hv : IsHomogeneous b v) :
      IsHomogeneous (a + b) ⁅u, v⁆

def HomogeneousSubmodule (a : RootLattice) : Submodule ℚ (FreeLieAlgebra ℚ (Generators (Fin 10))) where
  carrier := { u | IsHomogeneous a u }
  add_mem' hu hv := IsHomogeneous.add a _ _ hu hv
  zero_mem' := IsHomogeneous.zero a
  smul_mem' c u hu := IsHomogeneous.smul a c u hu

theorem free_bracket_homogeneous (a b : RootLattice) (u v : FreeLieAlgebra ℚ (Generators (Fin 10)))
    (hu : u ∈ HomogeneousSubmodule a) (hv : v ∈ HomogeneousSubmodule b) :
    ⁅u, v⁆ ∈ HomogeneousSubmodule (a + b) :=
  IsHomogeneous.bracket a b u v hu hv

/-!
# 3. Homogeneous Serre Ideal and Quotient Grading
-/
/-- We define homogeneity directly on the quotient (the Serre Algebra) by projecting the homogeneous elements. -/
def SerreHomogeneousSubmodule (a : RootLattice) : Submodule ℚ SerreAlgebra :=
  Submodule.map (CartanMatrix.Relations.toIdeal ℚ cartanMatrix).mkQ (HomogeneousSubmodule a)

theorem serre_bracket_homogeneous (a b : RootLattice) 
    (u v : SerreAlgebra)
    (hu : u ∈ SerreHomogeneousSubmodule a) (hv : v ∈ SerreHomogeneousSubmodule b) :
    ⁅u, v⁆ ∈ SerreHomogeneousSubmodule (a + b) := by
  rcases hu with ⟨u', hu', rfl⟩
  rcases hv with ⟨v', hv', rfl⟩
  use ⁅u', v'⁆
  constructor
  · exact free_bracket_homogeneous a b u' v' hu' hv'
  · rfl

/-!
# 4. Define height cutoffs and prove bracket bounds
-/
def height (a : RootLattice) : ℤ :=
  (a 0) + (a 1) + (a 2) + (a 3) + (a 4) + (a 5) + (a 6) + (a 7) + (a 8) + (a 9)

theorem height_add (a b : RootLattice) : height (a + b) = height a + height b := by
  dsimp [height]
  ring
  linarith

def HeightCutoff (N : ℕ) : Submodule ℚ SerreAlgebra :=
  ⨆ (a : RootLattice) (_ : |height a| ≤ N), SerreHomogeneousSubmodule a

theorem cutoff_bracket (N M : ℕ) (u v : SerreAlgebra)
    (hu : u ∈ HeightCutoff N) (hv : v ∈ HeightCutoff M) :
    ⁅u, v⁆ ∈ HeightCutoff (N + M) := by
  sorry

/-!
# 5. Form the ModuleCat colimit and transport its bracket
-/

def HeightSystem : ℕ ⥤ ModuleCat ℚ where
  obj N := ModuleCat.of ℚ (HeightCutoff N)
  map {N M} h := ModuleCat.ofHom (Submodule.inclusion (by sorry))
  map_id := by sorry
  map_comp := by sorry

def HeightColimit := colimit HeightSystem

-- Transport the bracket to the categorical colimit using the comparison map
-- (Implementation follows the AffineKacMoody colimit archetype)

end InfoGeometry.Lie.E10
