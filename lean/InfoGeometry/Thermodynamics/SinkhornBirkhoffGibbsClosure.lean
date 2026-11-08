/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Thermodynamics.SinkhornBirkhoffGibbsBridge

open scoped BigOperators

namespace InfoGeometry.Thermodynamics.SinkhornBirkhoff

variable {M N : Type*}

/-- Total mass is independent of whether a finite coupling is summed by rows or columns. -/
theorem sinkhorn_total_mass_conservation [Fintype M] [Fintype N]
    (P : M → N → ℝ) :
    ∑ m : M, rowMarginal P m = ∑ n : N, colMarginal P n := by
  simp only [rowMarginal, colMarginal]
  exact Finset.sum_comm

/-- The coupled scaling equations are equivalent to the doubly-stochastic property. -/
theorem sinkhorn_doublyStochastic_iff_coupled_scaling [Fintype N]
    (E : RegularizationParam) (C : N → N → ℝ) (S : ScalingPotentials N N) :
    IsDoublyStochastic (sinkhornCoupling E C S) ↔
      (∀ i : N, S.u i * (∑ j : N, gibbsKernel E C i j * S.v j) = 1) ∧
      (∀ j : N, S.v j * (∑ i : N, S.u i * gibbsKernel E C i j) = 1) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      rw [← sinkhorn_row_marginal]
      exact h.2.1 i
    · intro j
      rw [← sinkhorn_col_marginal]
      exact h.2.2 j
  · rintro ⟨hu, hv⟩
    exact sinkhorn_doublyStochastic_of_coupled_scaling E C S hu hv

end InfoGeometry.Thermodynamics.SinkhornBirkhoff
