/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Cantor.CantorRandomWalk
import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Symmetries of transition matrices on the Cantor-word carrier

For a matrix of transition weights on `CantorWord`, its symmetry group is the
subgroup of permutations that preserve every matrix entry under simultaneous
relabeling of source and target states. This definition concerns matrix
weights; a Markov-kernel or probability-measure structure requires additional
normalization and measurability data.
-/

namespace InfoGeometry.Cantor.MarkovMatrixSymmetry

open InfoGeometry.Cantor.CantorRandomWalk

/-- A permutation preserves a transition matrix when it preserves every
source-target weight. -/
def PreservesTransitionMatrix {ι : Type*} (P : Matrix ι ι ℝ)
    (σ : Equiv.Perm ι) : Prop :=
  ∀ i j, P (σ i) (σ j) = P i j

/-- The group of state relabelings that preserve a transition matrix. -/
def transitionMatrixSymmetryGroup {ι : Type*} (P : Matrix ι ι ℝ) :
    Subgroup (Equiv.Perm ι) where
  carrier := {σ | PreservesTransitionMatrix P σ}
  one_mem' := by
    intro i j
    rfl
  mul_mem' := by
    intro σ τ hσ hτ i j
    change P (σ (τ i)) (σ (τ j)) = P i j
    calc
      P (σ (τ i)) (σ (τ j)) = P (τ i) (τ j) := hσ (τ i) (τ j)
      _ = P i j := hτ i j
  inv_mem' := by
    intro σ hσ i j
    have h := hσ (σ⁻¹ i) (σ⁻¹ j)
    simpa using h.symm

/-- The transition-matrix symmetry group for weights indexed by the Cantor
binary-sequence carrier. -/
abbrev cantorTransitionSymmetryGroup (P : Matrix CantorWord CantorWord ℝ) :=
  transitionMatrixSymmetryGroup P

/-- Members of the Cantor transition symmetry group preserve each matrix
entry. -/
theorem cantorTransitionSymmetry_preserves (P : Matrix CantorWord CantorWord ℝ)
    (σ : cantorTransitionSymmetryGroup P) (x y : CantorWord) :
    P (σ.val x) (σ.val y) = P x y :=
  σ.property x y

end InfoGeometry.Cantor.MarkovMatrixSymmetry
