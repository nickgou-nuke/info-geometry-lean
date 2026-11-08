import InfoGeometry.Inference.PoissonUnbalancedSinkhorn
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite balanced transport plans

This owner isolates the finite fixed-marginal coupling layer.  It is a
transport-plan interface, not a definition of a Wasserstein distance or of a
continuous optimal-transport problem.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Row Col : Type*}
  [Fintype Row] [Nonempty Row] [Fintype Col] [Nonempty Col]

/-- A nonnegative finite coupling with prescribed row and column marginals. -/
structure FiniteBalancedTransportPlan (rowMass : Row → ℝ) (colMass : Col → ℝ) where
  coupling : Row → Col → ℝ
  coupling_nonneg : ∀ i j, 0 ≤ coupling i j
  row_marginal : ∀ i, transportRowMass coupling i = rowMass i
  col_marginal : ∀ j, transportColMass coupling j = colMass j

/-! The two marginal specifications necessarily have the same total mass. -/
omit [Nonempty Row] [Nonempty Col] in
theorem FiniteBalancedTransportPlan.total_mass_eq
    {rowMass : Row → ℝ} {colMass : Col → ℝ}
    (T : FiniteBalancedTransportPlan rowMass colMass) :
    (∑ i : Row, rowMass i) = ∑ j : Col, colMass j := by
  calc
    (∑ i : Row, rowMass i) = ∑ i : Row, transportRowMass T.coupling i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (T.row_marginal i).symm
    _ = ∑ j : Col, transportColMass T.coupling j := by
      unfold transportRowMass transportColMass
      rw [Finset.sum_comm]
    _ = ∑ j : Col, colMass j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact T.col_marginal j

omit [Nonempty Row] [Nonempty Col] in
/-- The finite transport cost is nonnegative for a pointwise nonnegative cost. -/
theorem FiniteBalancedTransportPlan.transport_cost_nonneg
    {rowMass : Row → ℝ} {colMass : Col → ℝ}
    (T : FiniteBalancedTransportPlan rowMass colMass)
    (cost : Row → Col → ℝ)
    (hcost : ∀ i j, 0 ≤ cost i j) :
    0 ≤ ∑ i : Row, ∑ j : Col, T.coupling i j * cost i j := by
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg (T.coupling_nonneg i j) (hcost i j)

end InfoGeometry.Inference
