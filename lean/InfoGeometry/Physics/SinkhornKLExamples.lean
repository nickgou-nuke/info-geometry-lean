/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.FiniteLogSinkhornConvergence

/-!
# Boundaries of the positive Sinkhorn theorem

Balancing does not imply invertibility. Structural-zero kernels need support
hypotheses: an upper-triangular kernel with a positive diagonal need not admit a
strictly positive diagonal scaling with both marginals equal to one.
-/
noncomputable section
open scoped BigOperators
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections

/-- A positive doubly stochastic matrix can have rank one. -/
def rankOneBalanced : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1 / 2

theorem rankOneBalanced_positive_singular :
    (∀ i j, 0 < rankOneBalanced i j) ∧
      rankOneBalanced ∈ doublyStochastic ℝ (Fin 2) ∧ rankOneBalanced.det = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    norm_num [rankOneBalanced]
  · rw [mem_doublyStochastic_iff_sum]
    constructor
    · intro i j
      norm_num [rankOneBalanced]
    constructor <;> intro k <;> norm_num [rankOneBalanced, Fin.sum_univ_two]
  · norm_num [Matrix.det_fin_two, rankOneBalanced]

/-- Positive diagonal entries alone do not supply total support for scaling. -/
def triangularKernel : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

theorem triangularKernel_no_positive_balanced_scaling
    (u v : Fin 2 → ℝ) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) :
    ¬ ((∀ i, rowMass (fun i j => u i * triangularKernel i j * v j) i = 1) ∧
       (∀ j, colMass (fun i j => u i * triangularKernel i j * v j) j = 1)) := by
  rintro ⟨hr, hc⟩
  have hr₀ := hr 0
  have hc₀ := hc 0
  norm_num [rowMass, colMass, triangularKernel, Fin.sum_univ_two] at hr₀ hc₀
  have hpos : 0 < u 0 * v 1 := mul_pos (hu 0) (hv 1)
  nlinarith

end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
