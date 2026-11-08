/- Birkhoff Polytope and Tangent Cone -/
/- Defines the Birkhoff Polytope constraints and Tangent Cone for the 
   Birkhoff Spectral Descent optimization framework. -/

import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
def IsDoublyStochastic (W : Matrix n n ℝ) : Prop :=
  (∀ i j, (0 : ℝ) ≤ W i j) ∧
    (∀ i, ∑ j, W i j = 1) ∧
      (∀ j, ∑ i, W i j = 1)

/- 
  The Tangent Cone at a state W ∈ ℬ_n. 
  The set of all allowable irrotational metric flows (gradients) A that 
  preserve the thermodynamic probability boundaries.
-/
def IsInTangentCone (W A : Matrix n n ℝ) : Prop :=
  (∀ i, ∑ j, A i j = 0) ∧
    (∀ j, ∑ i, A i j = 0) ∧
      (∀ i j, W i j = 0 → (0 : ℝ) ≤ A i j)

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
  constructor
  · intro h i
    have hi := h i
    have hsum :
        ∑ j, (W i j + η * A i j) = ∑ j, W i j := by
      rw [Finset.sum_add_distrib]
      have hscaled : ∑ j, η * A i j = 0 := by
        rw [← Finset.mul_sum, h_tan.1 i, mul_zero]
      rw [hscaled, add_zero]
    simp [BirkhoffDualAscentStep] at hi
    rw [hsum] at hi
    exact hi
  · intro h i
    have hsum :
        ∑ j, (W i j + η * A i j) = ∑ j, W i j := by
      rw [Finset.sum_add_distrib]
      have hscaled : ∑ j, η * A i j = 0 := by
        rw [← Finset.mul_sum, h_tan.1 i, mul_zero]
      rw [hscaled, add_zero]
    simp [BirkhoffDualAscentStep]
    rw [hsum, h i]

end InfoGeometry.Optimization
