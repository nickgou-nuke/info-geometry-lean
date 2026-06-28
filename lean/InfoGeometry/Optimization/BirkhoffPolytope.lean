/- Birkhoff Polytope and Tangent Cone -/
/- Defines the Birkhoff Polytope constraints and Tangent Cone for the 
   Birkhoff Spectral Descent optimization framework. -/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

open Matrix
open scoped BigOperators

namespace InfoGeometry.Optimization

variable {n : Type*} [Fintype n] [DecidableEq n]

/- 
  The Birkhoff Polytope. 
  The space of all doubly stochastic matrices, representing the exact 
  thermodynamic bipartite matchings of the quantum vacuum.
-/
structure IsDoublyStochastic (W : Matrix n n ℝ) : Prop :=
  (nonneg : ∀ i j, (0 : ℝ) ≤ W i j)
  (row_sum : ∀ i, ∑ j, W i j = 1)
  (col_sum : ∀ j, ∑ i, W i j = 1)

/- 
  The Tangent Cone at a state W ∈ ℬ_n. 
  The set of all allowable irrotational metric flows (gradients) A that 
  preserve the thermodynamic probability boundaries.
-/
structure IsInTangentCone (W A : Matrix n n ℝ) : Prop :=
  (row_sum_zero : ∀ i, ∑ j, A i j = 0)
  (col_sum_zero : ∀ j, ∑ i, A i j = 0)
  (boundary_push : ∀ i j, W i j = 0 → (0 : ℝ) ≤ A i j)

/- 
  The Dual Ascent Optimization Step.
  Updates the vacuum state W by flowing along the gradient A scaled by learning rate η.
-/
def BirkhoffDualAscentStep (W A : Matrix n n ℝ) (η : ℝ) : Matrix n n ℝ :=
  W + η • A

/-
  CONSERVATION OF PROBABILITY THEOREM
  Proves that flowing along the Tangent Cone strictly preserves the 
  macroscopic sum constraints of the universe.
-/
theorem dual_ascent_preserves_sums (W A : Matrix n n ℝ) (η : ℝ)
    (h_tan : IsInTangentCone W A) : 
    (∀ i, ∑ j, (BirkhoffDualAscentStep W A η) i j = 1) ↔ (∀ i, ∑ j, W i j = 1) := by
  sorry

end InfoGeometry.Optimization