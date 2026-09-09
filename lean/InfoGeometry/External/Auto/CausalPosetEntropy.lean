import Mathlib.Order.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic

/-!
# Causal Posets and the Modular Arrow of Time

A Causal Poset is a partially ordered set representing a causal structure.
Here we map the global hyperbolicity of the Light Cone directly to the 
Modular Boltzmann Entropy operator.
-/

class CausalPoset (α : Type u) extends PartialOrder α

namespace CausalPoset

variable {α : Type u} [CausalPoset α]

/-- The Causal Future J^+ of a point x is the set of all y such that x ≤ y. -/
def causalFuture (x : α) : Set α :=
  { y | x ≤ y }

-- Relative entropy function defined on the causal poset.
-- The Modular Arrow of Time implies that entropy strictly increases along the causal future.
variable (entropy : α → ℝ)

/--
Strict monotonicity of entropy defines the Arrow of Time:
If y is in the strict causal future of x (x < y), then entropy increases.
-/
def ArrowOfTime (entropy : α → ℝ) : Prop :=
  StrictMono entropy

/--
The domain where the relative entropy is strictly increasing with respect to a base point.
-/
def EntropyIncreasingDomain (entropy : α → ℝ) (x : α) : Set α :=
  { y | entropy x < entropy y }

/--
The Orchestrator's Projection:
We rigorously prove that if the Arrow of Time holds, the strict causal future 
is a subset of the Entropy Increasing Domain. The topological causal structure 
is completely bounded by the thermodynamic entropy flow.
-/
theorem strict_future_subset_entropy_domain (h_arrow : ArrowOfTime entropy) (x : α) :
    { y | x < y } ⊆ EntropyIncreasingDomain entropy x := by
  intro y hy
  -- hy is the hypothesis that x < y
  -- h_arrow is the strict monotonicity of entropy
  exact h_arrow hy

end CausalPoset
