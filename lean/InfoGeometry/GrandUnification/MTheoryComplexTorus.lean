import Mathlib

namespace InfoGeometry.GrandUnification

open scoped Manifold Topology
open scoped ContDiff
open scoped Pointwise
open Set

/-!
# M-Theory Compactification Target (Complex Torus)

The complex torus `V ⧸ L.toAddSubgroup` where `L` is a full-rank ℤ-lattice in a
finite-dimensional ℂ-vector space `V`.

This rigorously models the M-Theory compactification target spaces, preventing the 
hallucination of analytical boundaries by strictly typing the torus algebraically 
via discrete ℤ-lattices.
-/

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The complex torus `V ⧸ L.toAddSubgroup`. -/
abbrev ComplexTorus : Type _ := V ⧸ L.toAddSubgroup

namespace ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]

instance instT2Space : T2Space (ComplexTorus V L) := by
  have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  have : IsClosed (L.toAddSubgroup : Set V) := AddSubgroup.isClosed_of_discreteTopology
  exact inferInstance

instance instConnectedSpace : ConnectedSpace (ComplexTorus V L) :=
  Function.Surjective.connectedSpace QuotientAddGroup.mk_surjective
    continuous_quotient_mk'

instance instCompactSpace : CompactSpace (ComplexTorus V L) := by
  rw [← isCompact_univ_iff]
  simpa [Set.range_quotient_mk'] using
    (IsZLattice.isCompact_range_of_periodic L (QuotientAddGroup.mk' L.toAddSubgroup)
      continuous_quotient_mk' (by
        intro z w hw
        exact Quotient.sound' <| by
          rw [QuotientAddGroup.leftRel_apply]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw))

end ComplexTorus
end InfoGeometry.GrandUnification
