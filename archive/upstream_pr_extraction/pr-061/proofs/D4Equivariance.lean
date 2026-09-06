import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

import Mathlib.Data.Real.Basic

open Matrix

/-!
# D4 Equivariance of the Patch Feature Map

This module formalizes the symmetry constraints on our feature extraction.
If an image patch is rotated or reflected (an operation in D₄, the symmetries of a square),
the resulting structure tensor (or feature map) must rotate or reflect in exactly the same way.
-/

abbrev Patch2x2 := Matrix (Fin 2) (Fin 2) ℝ

/-- D4 is the Dihedral group of a square (8 elements) -/
abbrev D4 := DihedralGroup 4

/- The action of D4 on the grid indices (Fin 2 × Fin 2) -/
variable (gridAction : D4 → (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))

/-- 
The action of D4 on the patch itself. 
We pull back the values from the transformed indices.
-/
def patchAction (g : D4) (P : Patch2x2) : Patch2x2 :=
  fun i j => 
    let idx := gridAction g⁻¹ (i, j)
    P idx.1 idx.2

/-- 
A feature map is equivariant if applying the symmetry to the patch 
yields the exact same result as applying the symmetry to the extracted features.
-/
def IsEquivariant (featureMap : Patch2x2 → Patch2x2) : Prop :=
  ∀ (g : D4) (P : Patch2x2), 
    featureMap (patchAction gridAction g P) = patchAction gridAction g (featureMap P)

/-- 
Theorem: The identity map is trivially D4-equivariant.
-/
theorem identity_is_equivariant :
    IsEquivariant gridAction id := by
  dsimp [IsEquivariant]
  intro g P
  rfl
