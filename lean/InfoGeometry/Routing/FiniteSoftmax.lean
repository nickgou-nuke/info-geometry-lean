import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Finite softmax weights.

This owner proves positivity and normalization only.  It does not assert
equivariance, uniqueness of an annealing limit, or expert-balance properties.
-/

namespace InfoGeometry.Routing.FiniteSoftmax

open scoped BigOperators

noncomputable def partitionZ {G : Type*} [Fintype G]
    (score : G → ℝ) (tau : ℝ) : ℝ :=
  ∑ g, Real.exp (score g / tau)

noncomputable def weight {G : Type*} [Fintype G]
    (score : G → ℝ) (tau : ℝ) (g : G) : ℝ :=
  Real.exp (score g / tau) / partitionZ score tau

theorem partitionZ_pos {G : Type*} [Fintype G] [Nonempty G]
    (score : G → ℝ) (tau : ℝ) :
    0 < partitionZ score tau := by
  unfold partitionZ
  apply Finset.sum_pos'
  · intro g hg
    exact le_of_lt (Real.exp_pos _)
  · obtain ⟨g⟩ := ‹Nonempty G›
    exact ⟨g, Finset.mem_univ _, Real.exp_pos _⟩

theorem weight_pos {G : Type*} [Fintype G] [Nonempty G]
    (score : G → ℝ) (tau : ℝ) (g : G) :
    0 < weight score tau g := by
  unfold weight
  exact div_pos (Real.exp_pos _) (partitionZ_pos score tau)

theorem weight_sum_one {G : Type*} [Fintype G] [Nonempty G]
    (score : G → ℝ) (tau : ℝ) :
    ∑ g, weight score tau g = 1 := by
  unfold weight
  rw [← Finset.sum_div]
  change partitionZ score tau / partitionZ score tau = 1
  exact div_self (ne_of_gt (partitionZ_pos score tau))

end InfoGeometry.Routing.FiniteSoftmax
