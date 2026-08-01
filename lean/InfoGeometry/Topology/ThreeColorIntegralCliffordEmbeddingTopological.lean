import InfoGeometry.Canonical.ThreeColorIntegralCliffordEmbedding

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-! The coordinate carrier has its native discrete topology.  The statements in
this file are deliberately limited to continuity and closedness; no octonion
multiplication is used by the linear intersection layer. -/

theorem continuous_redCoordinateEmbedding :
    Continuous redCoordinateEmbedding := by
  exact continuous_of_discreteTopology

theorem continuous_greenCoordinateEmbedding :
    Continuous greenCoordinateEmbedding := by
  exact continuous_of_discreteTopology

theorem continuous_blueCoordinateEmbedding :
    Continuous blueCoordinateEmbedding := by
  exact continuous_of_discreteTopology

theorem isClosed_sharedIntegralHyperbolicAxis :
    IsClosed (sharedIntegralHyperbolicAxis : Set StandardIntegralSplitOctonion) := by
  exact isClosed_discrete _

theorem isClosed_redIntegralSector :
    IsClosed (redIntegralSector : Set StandardIntegralSplitOctonion) := by
  exact isClosed_discrete _

theorem isClosed_greenIntegralSector :
    IsClosed (greenIntegralSector : Set StandardIntegralSplitOctonion) := by
  exact isClosed_discrete _

theorem isClosed_blueIntegralSector :
    IsClosed (blueIntegralSector : Set StandardIntegralSplitOctonion) := by
  exact isClosed_discrete _

end InfoGeometry.Topology
