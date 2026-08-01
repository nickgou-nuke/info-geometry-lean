import InfoGeometry.Canonical.ThreeColorIntegralCliffordEmbedding
import InfoGeometry.Canonical.CubicJordanOsTopologicalReadout

namespace InfoGeometry.Topology

open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-! The native coordinate topology is discrete.  Consequently the typed
    colour placements and their finite-coordinate readouts are continuous,
    while the shared axis is closed. -/

theorem continuous_redEmbedding :
    Continuous (redEmbedding : ChiralCoefficients → SplitOct) := by
  exact continuous_of_discreteTopology

theorem continuous_greenEmbedding :
    Continuous (greenEmbedding : ChiralCoefficients → SplitOct) := by
  exact continuous_of_discreteTopology

theorem continuous_blueEmbedding :
    Continuous (blueEmbedding : ChiralCoefficients → SplitOct) := by
  exact continuous_of_discreteTopology

theorem isClosed_sharedIntegralHyperbolicAxis :
    IsClosed (sharedIntegralHyperbolicAxis : Set SplitOct) := by
  exact isClosed_discrete _

end InfoGeometry.Topology
