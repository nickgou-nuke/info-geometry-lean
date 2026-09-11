import InfoGeometry.Canonical.ColimitPartitionXiIdentificationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite primon partition refinement

This owner records the exact algebraic refinement law for finite partition
stages.  It does not introduce a limit, convergence statement, or an
identification with `riemannXi`: those are separate analytic obligations.
-/

noncomputable section

namespace InfoGeometry.Canonical.ColimitPartitionXiIdentification

open scoped BigOperators

/-- Disjoint finite stages factor exactly when they are adjoined. -/
theorem finitePrimonPartition_union
    {S U : Finset ℕ} (hSU : Disjoint S U) (s : ℂ) :
    finitePrimonPartition (S ∪ U) s =
      finitePrimonPartition S s * finitePrimonPartition U s := by
  unfold finitePrimonPartition
  rw [Finset.prod_union hSU]

end InfoGeometry.Canonical.ColimitPartitionXiIdentification
