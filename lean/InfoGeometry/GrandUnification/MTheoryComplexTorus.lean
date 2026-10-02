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
def ComplexTorus : Type _ := V ⧸ L.toAddSubgroup

namespace ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]

instance instAddCommGroup : AddCommGroup (ComplexTorus V L) :=
  inferInstanceAs (AddCommGroup (V ⧸ L.toAddSubgroup))

instance instTopologicalSpace : TopologicalSpace (ComplexTorus V L) :=
  inferInstanceAs (TopologicalSpace (V ⧸ L.toAddSubgroup))

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ComplexTorus V L) :=
  inferInstanceAs (IsTopologicalAddGroup (V ⧸ L.toAddSubgroup))

instance instT2Space : T2Space (ComplexTorus V L) := by
  letI : IsClosed (L.toAddSubgroup : Set V) :=
    AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  letI : T1Space (V ⧸ L.toAddSubgroup) :=
    inferInstance
  simpa [ComplexTorus] using (inferInstance : T2Space (V ⧸ L.toAddSubgroup))

instance instConnectedSpace : ConnectedSpace (ComplexTorus V L) :=
  Function.Surjective.connectedSpace QuotientAddGroup.mk_surjective
    continuous_quotient_mk'

instance instCompactSpace : CompactSpace (ComplexTorus V L) := by
  rw [← isCompact_univ_iff]
  simpa [ComplexTorus, Set.range_quotient_mk'] using
    (IsZLattice.isCompact_range_of_periodic L (QuotientAddGroup.mk' L.toAddSubgroup)
      continuous_quotient_mk' (by
        intro z w hw
        exact Quotient.sound' <| by
          rw [QuotientAddGroup.leftRel_apply]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw))

end ComplexTorus
end InfoGeometry.GrandUnification
