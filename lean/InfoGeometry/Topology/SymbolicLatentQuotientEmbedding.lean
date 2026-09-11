import InfoGeometry.Topology.SymbolicLatentSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Compact observational quotients

For a compact latent carrier, the quotient by equality of all finite
observables embeds as a closed subspace of the finite observation space.
This is a topological statement about the existing observational quotient;
it does not add a probabilistic or physical interpretation.
-/

namespace InfoGeometry.Topology

theorem symbolicObservationQuotient_isClosedEmbedding
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Topology.IsClosedEmbedding (symbolicObservationQuotientMap S) := by
  apply Continuous.isClosedEmbedding
  · exact continuous_symbolicObservationQuotientMap S
  · exact injective_symbolicObservationQuotientMap S

end InfoGeometry.Topology
