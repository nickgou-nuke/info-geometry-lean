import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Separation.Basic
import InfoGeometry.Canonical.YangianLevelZeroRepresentation
import InfoGeometry.Topology.YangianCoproductTensorActionTopological

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-!
# Topological level-zero invariant loci

This owner applies the generic closed-zero-locus theorem to Mathlib's native
Lie-module action.  It still makes no claim about level-one Yangian data.
-/

variable {R L V : Type*}
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]

/-- The locus annihilated by one level-zero Lie generator. -/
def levelZeroInvariantLocus (x : L) : Set V :=
  {v | IsLevelZeroInvariant (R := R) x v}

/-- Continuity of the evaluated Lie action makes its invariant locus closed. -/
theorem isClosed_levelZeroInvariantLocus
    [TopologicalSpace V] [T1Space V]
    (x : L) (hcont : Continuous (levelZeroAction (R := R) (V := V) x)) :
    IsClosed (levelZeroInvariantLocus (R := R) (L := L) (V := V) x) := by
  change IsClosed ((levelZeroAction (R := R) x) ⁻¹' ({0} : Set V))
  exact isClosed_singleton.preimage hcont

end InfoGeometry.Topology
