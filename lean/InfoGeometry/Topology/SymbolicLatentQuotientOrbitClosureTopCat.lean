import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosure

namespace InfoGeometry.Topology

/-!
Topological packaging of a modular-flow orbit closure.

This owner records only the native closed-subspace facts.  Transport of the
closure by the flow is kept in the preceding orbit-closure owner, so this
file does not introduce an unproved subtype homeomorphism.
-/

abbrev SymbolicLatentOrbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) :=
  {x // x ∈ K.orbitClosure q}

def symbolicLatentOrbitClosureInclusion
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) :
    TopCat.of (SymbolicLatentOrbitClosure K q) ⟶ TopCat.of Q :=
  TopCat.ofHom
    { toFun := (Subtype.val : SymbolicLatentOrbitClosure K q → Q)
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentOrbitClosure_isClosedEmbedding
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) :
    Topology.IsClosedEmbedding
      (Subtype.val : SymbolicLatentOrbitClosure K q → Q) := by
  exact (K.isClosed_orbitClosure q).isClosedEmbedding_subtypeVal

theorem isCompact_symbolicLatentOrbitClosure
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q] [CompactSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) :
    IsCompact (K.orbitClosure q) := by
  exact IsCompact.of_isClosed_subset isCompact_univ
    (K.isClosed_orbitClosure q) (Set.subset_univ _)

end InfoGeometry.Topology
