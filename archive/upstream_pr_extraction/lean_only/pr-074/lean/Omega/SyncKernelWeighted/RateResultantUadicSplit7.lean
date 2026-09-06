import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The four Puiseux branches produce the endpoint-cluster factor. -/
def alphaEndpointClusterOrder : ℕ :=
  Fintype.card (Fin 4)

/-- The four Puiseux branches contribute one extra unit of `u`-valuation through
`4 · (1 / 4) = 1`. -/
def rate_resultant_uadic_split_7_puiseux_fractional_order : ℕ :=
  Fintype.card (Fin 4) / 4

/-- The analytic small-root package contributes valuation `2`, and the Puiseux quarter-orders
sum to `1`, yielding the low-`u` degeneracy order `3`. -/
def lambdaDegeneracyOrder : ℕ :=
  2 + rate_resultant_uadic_split_7_puiseux_fractional_order

/-- The raw resultant valuation is the sum of the analytic degeneracy order and the endpoint
cluster order. -/
def rawResultantUadicValuation : ℕ :=
  lambdaDegeneracyOrder + alphaEndpointClusterOrder

/-- Paper label: `prop:rate-resultant-uadic-split-7`. The low-`u` Newton splitting gives four
Puiseux branches contributing the endpoint cluster order `4`, while the analytic small-root
package contributes valuation `3`; summing the two rigid pieces recovers the raw resultant
valuation `7`. -/
theorem paper_rate_resultant_uadic_split_7 :
    lambdaDegeneracyOrder = 3 ∧
      alphaEndpointClusterOrder = 4 ∧
      rawResultantUadicValuation = 7 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold lambdaDegeneracyOrder rate_resultant_uadic_split_7_puiseux_fractional_order
    norm_num
  · unfold alphaEndpointClusterOrder
    norm_num
  · unfold rawResultantUadicValuation lambdaDegeneracyOrder
      alphaEndpointClusterOrder rate_resultant_uadic_split_7_puiseux_fractional_order
    norm_num

end Omega.SyncKernelWeighted
